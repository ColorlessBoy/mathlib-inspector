import Lean
import Lean.Meta
import Std.Data.HashMap
import Mathlib

open Lean Meta Tactic
open Lean System Meta

-- 计算 Expr 的节点数，深度超过 maxSearchSize 时提前终止，返回 1
partial def getExprSize (e : Expr) (reward : Nat) : Nat :=
  if reward <= 0 then
    1 -- 超过最大深度，提前返回 1
  else
    match e with
    | Expr.bvar _ => 1
    | Expr.fvar _ => 1
    | Expr.mvar _ => 1
    | Expr.sort _ => 1
    | Expr.const _ _ => 1
    | Expr.app f arg =>
      let n1 := getExprSize f (reward - 1)
      let n2 := getExprSize arg (reward - n1 - 1)
      1 + n1 + n2
    | Expr.lam _ t body _ =>
      let n1 := getExprSize t (reward - 1)
      let n2 := getExprSize body (reward - n1 - 1)
      1 + n1 + n2
    | Expr.forallE _ t body _ =>
      let n1 := getExprSize t (reward - 1)
      let n2 := getExprSize body (reward - n1 - 1)
      1 + n1 + n2
    | Expr.letE _ t val body _ =>
      let n1 := getExprSize t (reward - 1)
      let n2 := getExprSize val (reward - n1 - 1)
      let n3 := getExprSize body (reward - n1 - n2 - 1)
      1 + n1 + n2 + n3
    | Expr.lit _ => 1
    | Expr.mdata _ e => 1 + getExprSize e (reward - 1)
    | Expr.proj _ _ e => 1 + getExprSize e (reward - 1)

def parseName (str : String) : Name :=
  let parts := str.splitOn "."
  parts.foldl (fun acc part =>
    if part.startsWith "«" && part.endsWith "»" then
      -- 去掉两边的 "«" 和 "»"
      let cleanPart := part.dropRight 1 |>.drop 1
      Name.mkStr acc cleanPart
    else if part.toNat?.isSome then
      -- 优先处理纯数字的部分
      Name.mkNum acc part.toNat!
    else
      -- 普通字符串标识符
      Name.mkStr acc part
  ) Name.anonymous

-- 判断是否是数学公理
def isMath (name : Name) : Bool :=
  name.toString.startsWith "Mathlib"

-- 判断是否是 Axiom
def isAxiom (constInfo : ConstantInfo) : Bool :=
  match constInfo with
  | ConstantInfo.axiomInfo _ => true
  | _ => false

def isInductive (constInfo : ConstantInfo) : Bool :=
  match constInfo with
  | ConstantInfo.inductInfo _ => true
  | _ => false

-- 获取所有 Axioms
def listAllAxioms : MetaM (List Name) := do
  let env ← getEnv
  let axioms := env.constants.toList.filter (λ (_, c) => isAxiom c)
  return axioms.map (fun (name, _) => name)

-- 获取所有 Inductive 工具
def listAllInductives: MetaM (List Name) := do
  let env ← getEnv
  let inductives := env.constants.toList.filter (λ (_, c) => isInductive c)
  return inductives.map (fun (name, _) => name)

-- 判断是否是 Axiom
def isTheorem (constInfo : ConstantInfo) : Bool :=
  match constInfo with
  | ConstantInfo.thmInfo _ => true
  | _ => false

-- 获取所有 Axioms
def listAllThms: MetaM (List Name) := do
  let env ← getEnv
  let thms := env.constants.toList.filter (λ (_, c) => isTheorem c)
  return thms.map (fun (name, _) => name)

def listAllConst: MetaM (List Name) := do
  let env ← getEnv
  let consts := env.constants.toList
  return consts.map (fun (name, _) => name)

def getPrefixLevel (e : Expr) : Nat :=
  match e with
  | Expr.bvar _ => 100
  | Expr.fvar _ => 100
  | Expr.mvar _ => 100
  | Expr.sort _ => 100
  | Expr.const _ _ => 100
  | Expr.app _ _=> 3
  | Expr.lam _ _ _ _ => 2
  | Expr.forallE _ _ _ _ => 1
  | Expr.letE _ _ _ _ _ => 100
  | Expr.lit _ => 100
  | Expr.mdata _ expr => getPrefixLevel expr
  | Expr.proj _ _ _ => 100

-- 将表达式转化为前缀表达式的字符串
partial def toPrefixExpr (e : Expr) (maxExprSize: Nat) : MetaM String := do
  let size := getExprSize e maxExprSize
  if size >= maxExprSize then
    return s!"Too large"
  match e with
  | Expr.bvar idx => pure s!"#{idx}"
  | Expr.fvar fvarId => pure s!"(FreeVar {fvarId.name})"
  | Expr.mvar mvarId => pure s!"(MetaVar {mvarId.name})"
  | Expr.sort lvl =>
    if lvl == 0 then
      return "Prop"
    pure s!"Sort({lvl})"
  | Expr.const n _ => pure s!"{n}"
  | Expr.app f arg =>
    let mut fStr ← toPrefixExpr f maxExprSize
    let mut argsStr ← toPrefixExpr arg maxExprSize
    let expr_level := getPrefixLevel e
    let f_level := getPrefixLevel f
    let arg_level := getPrefixLevel arg
    if f_level < expr_level then
      fStr := s!"({fStr})"
    if arg_level <= expr_level then
      argsStr := s!"({argsStr})"
    pure s!"{fStr} {argsStr}"
  | Expr.lam _ t body _ =>
    let mut bodyStr ← toPrefixExpr body maxExprSize
    let mut t_prefix ← toPrefixExpr t maxExprSize
    let expr_level := getPrefixLevel e
    let t_level := getPrefixLevel t
    let arg_level := getPrefixLevel body
    if t_level <= expr_level then
      t_prefix := s!"({t_prefix})"
    if arg_level < expr_level then
      bodyStr := s!"({bodyStr})"
    pure s!"{t_prefix} => {bodyStr}"
  | Expr.forallE _ t body _ =>
    let mut bodyStr ← toPrefixExpr body maxExprSize
    let mut t_prefix ← toPrefixExpr t maxExprSize
    let expr_level := getPrefixLevel e
    let t_level := getPrefixLevel t
    let arg_level := getPrefixLevel body
    if t_level <= expr_level then
      t_prefix := s!"({t_prefix})"
    if arg_level < expr_level then
      bodyStr := s!"({bodyStr})"
    pure s!"{t_prefix} -> {bodyStr}"
  | Expr.letE n _ value body _ => do
    -- 展开 let 的定义
    let valueStr ← toPrefixExpr value maxExprSize
    let bodyStr ← toPrefixExpr body maxExprSize
    pure s!"(Subst {n} := {valueStr} in {bodyStr})"
  | Expr.lit l =>
    match l with
    | Literal.natVal val => pure s!"(NatLiteral {val})"
    | Literal.strVal val => pure s!"(StrLiteral \"{val}\")"
  | Expr.mdata _ expr =>
    let bodyExpr ← toPrefixExpr expr maxExprSize
    pure s!"{bodyExpr}"
  | Expr.proj typeName idx struct =>
    let prefixStruct ← toPrefixExpr struct maxExprSize
    pure s!"(Proj {typeName} {idx} {prefixStruct})"

-- 提取常量的信息
def extractConstantDetails (name : Name) : MetaM (Expr × Option Expr) := do
  let env ← getEnv
  match env.find? name with
  | some (ConstantInfo.axiomInfo ax) =>
      -- 公理：只有类型，没有值
      return (ax.type, none)
  | some (ConstantInfo.thmInfo thm) =>
      -- 定理：有类型和证明值
      return (thm.type, some thm.value)
  | some (ConstantInfo.defnInfo defn) =>
      -- 定义：有类型和定义体
      return (defn.type, some defn.value)
  | some (ConstantInfo.ctorInfo ctor) =>
      -- 构造函数：有类型，但无单独定义值
      return (ctor.type, none)
  | some (ConstantInfo.recInfo rec) =>
      -- 消去规则（recursor）：有类型，但无定义值
      return (rec.type, none)
  | some (ConstantInfo.inductInfo ind) =>
      -- 归纳定义：有类型，但无定义值
      return (ind.type, none)
  | _ => throwError "Constant {name} not found or is not supported."

def getConstantDetails (name : Name) (maxPropSize : Nat := 1024) (maxProofSize : Nat := 10000): MetaM String := do
  let (type, value?) ← extractConstantDetails name
  let typeStr ← toPrefixExpr type maxPropSize
  match value? with
  | some value =>
    let valueStr ← toPrefixExpr value maxProofSize
    pure s!"{name}\n{typeStr}\n{valueStr}"
  | none =>
    pure s!"{name}\n{typeStr}"

-- 将 Axioms 写入文件
def saveAxiomListToFile (filePath : String) : MetaM Unit := do
  let axioms ← listAllAxioms
  let lines ← axioms.mapM (fun name => pure s!"{name}")
  let content := String.intercalate "\n" lines
  IO.FS.writeFile filePath content

-- 将 Inductive 工具写入文件
def saveInductiveListToFile (filePath : String) : MetaM Unit := do
  let tools ← listAllInductives
  let lines ← tools.mapM (fun name => pure s!"{name}")
  let content := String.intercalate "\n" lines
  IO.FS.writeFile filePath content

-- 将 Inductive 工具写入文件
def saveThmListToFile (filePath : String) : MetaM Unit := do
  let thms ← listAllThms
  let lines ← thms.mapM (fun name => pure s!"{name}")
  let content := String.intercalate "\n" lines
  IO.FS.writeFile filePath content

def getConstSize (info : ConstantInfo) (maxPropSize: Nat) (maxProofSize: Nat) : MetaM String := do
  match info with
  | (ConstantInfo.axiomInfo ax) =>
    let s1 := getExprSize ax.type maxPropSize
    pure s!"{s1} 0"
  | (ConstantInfo.thmInfo thm) =>
    let s1 := getExprSize thm.type maxPropSize
    let s2 := getExprSize thm.value maxProofSize
    pure s!"{s1} {s2}"
  | _ => pure s!"0 0"

-- 将 Inductive 工具写入文件
def saveConstAndSizeToFile (filePath : String) (maxPropSize: Nat) (maxProofSize: Nat) : MetaM Unit := do
  let env ← getEnv
  let consts := env.constants.toList.filter (λ (_, c) => isTheorem c)
  let mut contentList : List String := []
  let mut processedCount : Nat := 0
  let totalCount := consts.length
  for (name, const) in consts do
    processedCount := processedCount + 1
    let s ← getConstSize const maxPropSize maxProofSize
    contentList := contentList ++ [s!"{name} {s}"]
    -- 输出当前进度信息到终端
    IO.FS.writeFile "process.log" s!"Processing {processedCount}/{totalCount}: {name}"
  let content := String.intercalate "\n" contentList
  IO.FS.writeFile filePath content

-- 将 Inductive 工具写入文件
def saveConstListToFile (filePath : String) : MetaM Unit := do
  let consts ← listAllConst
  let lines ← consts.mapM (fun name => pure s!"{name}")
  let content := String.intercalate "\n" lines
  IO.FS.writeFile filePath content

-- 打印常量的信息，包括类型和可选的值
def printConstantDetails (name : Name) (maxPropSize: Nat := 1024) (maxProofSize: Nat := 10000) : MetaM Unit := do
  let (type, value?) ← extractConstantDetails name
  let typeStr ← toPrefixExpr type maxPropSize
  match value? with
  | some value =>
    let valueStr ← toPrefixExpr value maxProofSize
    logInfo s!"{name}\n  {typeStr}\n  {valueStr}"
  | none =>
    logInfo s!"{name}\n  {typeStr}"

-- 打印常量的信息，包括类型和可选的值
def printConstantDetailsV2 (name : String) (maxPropSize: Nat := 1024) (maxProofSize: Nat := 10000): MetaM Unit := do
  let (type, value?) ← extractConstantDetails (parseName name)
  let typeStr ← toPrefixExpr type maxPropSize
  match value? with
  | some value =>
    let valueStr ← toPrefixExpr value maxProofSize
    logInfo s!"{name}\n  {typeStr}\n  {valueStr}"
  | none =>
    logInfo s!"{name}\n  {typeStr}"

def extractPrefix (s : String) : String :=
  if s.startsWith "Lean." then
    s.drop 5 |>.take 2  -- 如果以 "Lean." 开头，取第6-7个字符
  else
    s.take 2            -- 否则取前两个字符

-- 计算字符串的哈希值
def stringHash (s : String) : UInt64 :=
  let modulus : UInt64 := 4294967311  -- 一个比 2^32 稍大的素数
  let multiplier : UInt64 := 131
  s.foldl (fun acc c => (acc * multiplier + UInt64.ofNat c.toNat) % modulus) 5381

def hashConstName (s: String) : String :=
  s

-- 将表达式转化为前缀表达式的字符串
partial def toPrefixExprCompact (e : Expr) (maxSize: Nat) : MetaM String := do
  let size := getExprSize e maxSize
  if size >= maxSize then
    return s!"Too large"
  match e with
  | Expr.bvar idx => pure s!"#{idx}"
  | Expr.fvar fvarId => pure s!"(F {fvarId.name})"
  | Expr.mvar mvarId => pure s!"(M {mvarId.name})"
  | Expr.sort lvl => pure s!"(S {lvl})"
  | Expr.const n _ =>
    let n_hashed := hashConstName n.toString
    pure s!"(C {n_hashed})"
  | Expr.app f arg =>
    let fStr ← toPrefixExprCompact f maxSize
    let argsStr ← toPrefixExprCompact arg maxSize
    pure s!"(A {fStr} {argsStr})"
  | Expr.lam _ t body _ =>
    let bodyStr ← toPrefixExprCompact body maxSize
    let t_prefix ← toPrefixExprCompact t maxSize
    pure s!"(L {t_prefix} {bodyStr})"
  | Expr.forallE _ t body _ =>
    let bodyStr ← toPrefixExprCompact body maxSize
    let t_prefix ← toPrefixExprCompact t maxSize
    pure s!"(F {t_prefix} {bodyStr})"
  | Expr.letE _ t value body _ => do
    let tStr ← toPrefixExprCompact t maxSize
    let valueStr ← toPrefixExprCompact value maxSize
    let bodyStr ← toPrefixExprCompact body maxSize
    pure s!"(Let {tStr} {valueStr} {bodyStr})"
  | Expr.lit l =>
    match l with
    | Literal.natVal val => pure s!"(NL {val})"
    | Literal.strVal val => pure s!"(SL \"{val}\")"
  | Expr.mdata _ expr =>
    let bodyExpr ← toPrefixExprCompact expr maxSize
    pure s!"{bodyExpr}"
  | Expr.proj typeName idx struct =>
    let prefixStruct ← toPrefixExprCompact struct maxSize
    pure s!"(P {typeName} {idx} {prefixStruct})"

def getConstantDetailsCompact (name : Name) (maxPropSize: Nat := 1024) (maxProofSize: Nat := 10000) : MetaM String := do
  let (type, value?) ← extractConstantDetails name
  let propSize := getExprSize type maxPropSize
  if propSize > maxPropSize then
    throwError "prop size is too large"
  let typeStr ← toPrefixExprCompact type maxPropSize
  let hashed_name := hashConstName name.toString
  match value? with
  | some value =>
    let proofSize := getExprSize value maxProofSize
    if proofSize > maxProofSize then
      pure s!"{hashed_name}\n{typeStr}"
    else
      let valueStr ← toPrefixExprCompact value maxProofSize
      pure s!"{hashed_name}\n{typeStr}\n{valueStr}"
  | none =>
    pure s!"{hashed_name}\n{typeStr}"

-- 在 IO 中运行 MetaM
def runMetaMInIO (metaCtx: Meta.Context) (metaState: Meta.State) (coreCtx: Core.Context) (coreStateRef : ST.Ref IO.RealWorld Core.State
)  (filePath: String) (constName : String) (maxPropSize: Nat := 1024) (maxProofSize: Nat := 10000) : IO Unit := do
  let res ← ((getConstantDetailsCompact (parseName constName) maxPropSize maxProofSize).run metaCtx metaState coreCtx coreStateRef).toBaseIO
  match res with
  | .ok (info, _) =>
    let output := info
    IO.FS.writeFile filePath output
    IO.println s!"Successfully wrote output for {constName}."
  | .error err =>
    let errorMsg ← err.toMessageData.toString
    IO.println s!"Error: {constName} {errorMsg}"

-- 主函数，支持动态交互
def mainLoop (outputDir: String) (thmsFilePath: String) (startThmIdx: Nat) (endThmIdx: Nat) (generateNewWords: Nat) (maxPropSize: Nat := 1024) (maxProofSize: Nat := 10000) : IO Unit := do
  let opts : Options := {}
  let env ← importModules #[{ module := `Init }, { module := `Std }, { module := `Mathlib }] opts
  let coreCtx : Core.Context := {
    options := opts,
    fileName := "<input>",
    fileMap := FileMap.ofString ""
  }
  -- 构造 MetaM.Context
  let lctx : LocalContext := {}
  let metaCtx : Meta.Context := {
    config := {},
    lctx := lctx,
    localInstances := #[],
    defEqCtx? := none
  }

  -- 构造 MetaM.State
  let metaState : Meta.State := {}
  let coreStateRef ← ST.mkRef { env := env } -- 初始化 Core.State

  if generateNewWords > 0 then
    IO.println s!"Generate new consts.txt"
    let _ ← ((saveConstListToFile "consts.txt").run metaCtx metaState coreCtx coreStateRef).toBaseIO
    IO.println s!"Generate new {thmsFilePath}"
    let _ ← ((saveThmListToFile thmsFilePath).run metaCtx metaState coreCtx coreStateRef).toBaseIO

  -- 读取 thmsFilePath 文件内容
  let thmsContent ← IO.FS.readFile thmsFilePath
  let thmNames := thmsContent.splitOn "\n" |>.filter (· ≠ "") -- 过滤空行

  let mut thmNames := thmNames.drop startThmIdx
  if endThmIdx > startThmIdx then
    thmNames := thmNames.take (endThmIdx - startThmIdx)

  IO.println s!"Start handle {thmNames.length} thms."

  -- 逐一处理文件中的常量名称
  for (idx, constName) in thmNames.enum do
    let hashedConstName := hashConstName constName
    let filePath := s!"{outputDir}/{hashedConstName}.txt"
    let fileExists ← FilePath.pathExists filePath
    if fileExists then
      IO.println s!"File {filePath} already exists."
    else
      IO.println s!"Processing {idx + startThmIdx} {constName}..."
      runMetaMInIO metaCtx metaState coreCtx coreStateRef filePath constName maxPropSize maxProofSize

  IO.println "All constants processed."

-- Lean 的入口
def main (args : List String) : IO Unit := do
  -- 检查是否提供了输出目录和文件路径参数
  if args.length == 0 then
    IO.println "Usage: MathlibInspector <thmsFilePath> <outputDir> ?<startThmIdx> ?<endThmIdx> ?<generateNewWords> ?<maxPropSize> ?<maxProofSize>"
    return
  let thmsFilePath := if args.length >= 1 then args.get! 0 else "thms.txt"
  let outputDir := if args.length >= 2 then args.get! 1 else "output"
  let startThmIdx := if args.length >= 3 then (args.get! 2).toNat! else 0
  let endThmIdx := if args.length >= 4 then (args.get! 3).toNat! else 0
  let generateNewWords := if args.length >= 5 then (args.get! 4).toNat! else 0
  let maxPropSize := if args.length >= 6 then (args.get! 5).toNat! else 1024
  let maxProofSize := if args.length >= 7 then (args.get! 6).toNat! else 10000

  let folderExists ← FilePath.pathExists outputDir
  if folderExists then
    IO.println s!"Directory {outputDir} already exists."
  else
    IO.FS.createDir outputDir
    IO.println s!"Directory {outputDir} created."

  mainLoop outputDir thmsFilePath startThmIdx endThmIdx generateNewWords maxPropSize maxProofSize

open Lean Elab Tactic Meta

-- 定义一个辅助函数，用于比较和拆分目标
def proofStep (flag : Expr)
    (action goal: Expr)
    (diffContext sameContext : List (Expr × Expr) := [])
    : MetaM (Option ((List Expr) × Array Expr)) := do
  -- 添加调试日志
  trace[Meta.debug] "ProofStep called with action: {action}, goal: {goal}"
  trace[Meta.debug] "Current diffContext: {diffContext}, sameContext: {sameContext}"

  if ← Meta.isDefEq action goal then
    trace[Meta.debug] "Action and goal are definitionally equal"
    let mut newGoals: List Expr := []
    for (fvar, ctxType) in diffContext.reverse do
      trace[Meta.debug] "Processing diffContext: {ctxType}"
      newGoals ← newGoals.mapM (fun g => mkForallFVars #[fvar] g)
      newGoals := ctxType :: newGoals
    trace[Meta.debug] "Processing sameContext"
    let sameFVars := (sameContext.map (fun (fvar, _)=>fvar)).toArray
    newGoals ← newGoals.mapM (fun g => mkForallFVars sameFVars g)
    trace[Meta.debug] "New goals: {newGoals}"
    return some (newGoals, sameFVars)

  match flag with
  | Expr.forallE _ _ flagBody _ =>
    match action with
    | Expr.forallE name ty body info =>
      trace[Meta.debug] "Action is a forall with name: {name}, type: {ty}"
      if diffContext.isEmpty then
        match goal with
        | Expr.forallE _ goalTy goalBody _ =>
          trace[Meta.debug] "Goal is also a forall with type: {goalTy}"
          -- 对 body 进行比较时，确保绑定变量一致
          if ← Meta.isDefEq ty goalTy then
            trace[Meta.debug] "Action and goal have same argument type."
            withLocalDecl name info ty fun fVar => do
              -- 递归调用 proofStep
              let action := body.instantiate1 fVar
              let goal := goalBody.instantiate1 fVar
              return ← proofStep flagBody action goal diffContext (sameContext ++ [⟨fVar, ty⟩])
          else
            trace[Meta.debug] "Action and goal have different argument type."
            withLocalDecl name info ty fun fVar => do
              let action := body.instantiate1 fVar
              return ← proofStep flagBody action goal (diffContext ++ [⟨fVar, ty⟩]) sameContext
        | _ =>
          trace[Meta.debug] "Goal is not a forall"
          withLocalDecl name info ty fun fVar => do
            let action := body.instantiate1 fVar
            return ← proofStep flagBody action goal (diffContext ++ [⟨fVar, ty⟩]) sameContext
      else
        trace[Meta.debug] "Adding to diffContext"
        withLocalDecl name info ty fun fVar => do
          let action := body.instantiate1 fVar
          return ← proofStep flagBody action goal (diffContext ++ [⟨fVar, ty⟩]) sameContext
    | _ =>
      trace[Meta.debug] "Action is not a forall"
      return none
  | _ =>
      trace[Meta.debug] "Flag is not a forall"
      return none

def postProcess (mainGoal: MVarId) (action: Expr) (solutionMVarIds : List MVarId) (sameFVars : Array Expr) : MetaM Unit := do
  let solutions := solutionMVarIds.map (Expr.mvar)
  trace[Meta.debug] "Collected solutions: {solutions}"
  -- 组装最终证明项
  let mut partSolutions : List Expr := []
  for solution in solutions do
    let mut g : Expr := solution
    for fvar in sameFVars do
      g := mkApp g fvar
    for solution in partSolutions do
      g := mkApp g solution
    partSolutions := partSolutions ++ [g]
  let mut rst := action
  for fvar in sameFVars do
    rst := mkApp rst fvar
  for solution in partSolutions do
    rst := mkApp rst solution
  rst ← mkForallFVars sameFVars rst
  trace[Meta.debug] "Collected rst: {rst}"
  mainGoal.assign rst

-- 定义 tactic，封装 proofStep 的逻辑
syntax (name := abstractTactic) "abstract_proof " term : tactic

@[tactic abstractTactic] def evalAbstractTactic : Tactic := fun stx =>
  match stx with
  | `(tactic| abstract_proof $actionExpr) => do
    -- 获取当前目标
    let mainGoal ← getMainGoal
    let goal ← mainGoal.getType

    -- 解析 action 表达式
    let action ← elabTerm actionExpr none
    let actionType ← inferType action

    -- 调用 proofStep
    match ← proofStep actionType actionType goal with
    | some (newGoals, sameFVars) =>
      if newGoals.isEmpty then
        -- 如果目标已被证明，表示成功结束
        trace[Meta.debug] "Goal proven successfully."
        mainGoal.assign action
        replaceMainGoal []
      else
        -- 替换目标并设置新目标
        let newGoalMVarExprs ← newGoals.mapM (fun type => mkFreshExprMVar type)
        let newGoalMVarIds := newGoalMVarExprs.map (Expr.mvarId!)
        trace[Meta.debug] "mvarExprs {newGoalMVarExprs}, mvarIds {newGoalMVarIds}"
        replaceMainGoal newGoalMVarIds
        withMainContext do
          postProcess mainGoal action newGoalMVarIds sameFVars
    | none =>
      throwError "Failed to abstract the proof step. Ensure action and goal are compatible."
  | _ => throwUnsupportedSyntax
