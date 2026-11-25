# 刑事法律体系 Lean 4 核心候选与全量验收

以下为项目历史工作记录。历次交付的文件状态以[归档说明](archive-scope.md)为准。

Lean 4 可以作为刑事法律统一体系的验证层，检查已明确建模的条件、例外、效力区间和推导关系。法律文本的翻译准确性、证据真实性及案件事实认定仍须独立复核。本页保存核心候选源码、分层验收条件及最新法源的接入事项；候选源码尚未经过 Lean 编译。

[统一体系总页](project-notes.md)。项目状态日期为2026年10月27日。1697页总稿及原资料包仍为此前交付版本；本轮没有生成新版PDF或源码ZIP。

# 全量目标的验收范围

国家法律法规数据库的859个司法解释版本记录属于母目录，包含不同法律部门和历史版本，不能直接当作859件现行刑事解释。所有记录须逐件分为刑事实体、刑事程序、通用或交叉适用、不在范围、待核，并保存分类依据。刑事相关的已废止和已修改版本仍须保留，以支持历史案件的时间效力判断。

立法解释、正式司法解释、司法解释性质文件、联合规范性文件、意见、会议纪要、案例及地方参数分别记录。有关文件可以通过引用关系接入同一体系，但不因此获得同一规范层级。修改或废止决定应连接到所修改或废止的具体版本和条款。

| 验收层 | 必须满足的条件 | 当前可确认的状态 |
| --- | --- | --- |
| 法源 | 正文、发布机关、文号、官方位置及原件摘要可追溯 | 前稿仍保留120项正文或版本缺口 |
| 效力 | 公布、施行、修正、废止及适用范围逐件有依据 | 全量效力链尚未验收 |
| 建模 | 每款、每项及独立分支均有规则和来源定位 | 前稿有条级首稿与62个解释专题，不能视为全部解释逐款完成 |
| Lean | 固定工具链后干净编译，目标声明无未许可公理依赖 | 本页仅候选源码，未编译 |
| 法律复核 | 中文释义与模型双向核对，正例、反例和边界例通过 | 不以程序编译代替法律复核 |

# Lean 模型的边界

法律规范与已经发生的行为分开表示；“应当排除”不会自动推出办案机关事实上已经排除。未知、已否定和存在认定冲突分别保留；缺乏某事实的证明不自动证明其反面。每个证据、案件、行为、主体和程序阶段必须有独立标识，补正结论必须绑定同一证据。

金额使用整数单位或有理数，避免浮点误差；日、月、年使用不同类型，不能统一将一个月换成30日。区间仅描述形式生效，具体案件的从旧兼从轻、司法解释时间效力及过渡条款须另行建模，不能由“今天有效”直接推出“适用本案”。

原型中的评估值均是需要外部证据和法律审查支持的输入，不是Lean自动认定的事实。规范函数输出的是局部规则是否触发；不触发本分支，不能直接推出证据可采、行为无罪或程序已经合法完成。

# 核心候选源码

以下代码拟保存为Core.lean，只依赖Lean标准库。它用于四值事实评估、规范与履行的分离、半开效力区间、刑诉法第55条局部门槛及第56条排除分支。代码未编译，所有定理和例子均处于待机器检查状态；不属于全法Lean化完成成果。

```lean
import Std

namespace CriminalSystem

/-
Uncompiled candidate. Assessed inputs require independent source and legal review.
No theorem here establishes real case facts or applicability to a real case.
-/

structure SourceRef where
  documentId : String
  versionId : String
  articleId : String
  officialUrl : String
  snapshotHash : Option String

/-- Day ordinals are supplied by an independently verified calendar conversion. -/
structure EffectWindow where
  starts : Nat
  endsExclusive : Option Nat

/-- Formal entry into force only; criminal retroactivity is a separate question. -/
def formallyInForce (w : EffectWindow) (day : Nat) : Prop :=
  w.starts ≤ day ∧
    match w.endsExclusive with
    | none => True
    | some stop => day < stop

theorem startIncluded :
    formallyInForce ⟨10, some 20⟩ 10 := by decide

theorem endExcluded :
    ¬ formallyInForce ⟨10, some 20⟩ 20 := by decide

inductive Assessment where
  | established | refuted | unknown | conflicting
  deriving DecidableEq, Repr

inductive Trigger where
  | triggered | notTriggered | unresolved
  deriving DecidableEq, Repr

def negateAssessment : Assessment → Assessment
  | .established => .refuted
  | .refuted => .established
  | .unknown => .unknown
  | .conflicting => .conflicting

/-- Conservative audit aggregation, NOT classical or Belnap conjunction. -/
def auditConjunction : Assessment → Assessment → Assessment
  | .conflicting, _ => .conflicting
  | _, .conflicting => .conflicting
  | .refuted, _ => .refuted
  | _, .refuted => .refuted
  | .established, .established => .established
  | _, _ => .unknown

def allAssessments (xs : List Assessment) : Assessment :=
  xs.foldr auditConjunction .established

def toTrigger : Assessment → Trigger
  | .established => .triggered
  | .refuted => .notTriggered
  | .unknown => .unresolved
  | .conflicting => .unresolved

theorem unknownNotRefuted :
    Assessment.unknown ≠ Assessment.refuted := by decide

theorem assessmentNegationInvolutive (a : Assessment) :
    negateAssessment (negateAssessment a) = a := by
  cases a <;> rfl

/-
CPP55 local gates only. "factsSupported" covers guilt and sentencing facts;
"evidenceVerified" requires verification through statutory procedure.
A passing evidence gate is not sufficient to order a conviction.
-/
structure CPP55Input where
  caseId : String
  onlyConfession : Assessment
  factsSupported : Assessment
  evidenceVerified : Assessment
  reasonableDoubtExcluded : Assessment

def cpp55ConvictionBar (f : CPP55Input) : Trigger :=
  toTrigger f.onlyConfession

def cpp55EvidenceGate (f : CPP55Input) : Trigger :=
  toTrigger (allAssessments [
    negateAssessment f.onlyConfession,
    f.factsSupported,
    f.evidenceVerified,
    f.reasonableDoubtExcluded])

def confessionOnlySample : CPP55Input :=
  ⟨"synthetic-case", .established, .unknown, .unknown, .unknown⟩

def evidenceGateSample : CPP55Input :=
  ⟨"synthetic-case", .refuted, .established, .established, .established⟩

theorem confessionOnlyBarsConviction :
    cpp55ConvictionBar confessionOnlySample = .triggered := by decide

theorem assessedEvidenceGatePasses :
    cpp55EvidenceGate evidenceGateSample = .triggered := by decide

theorem unresolvedDoubtDoesNotPass :
    cpp55EvidenceGate
      { evidenceGateSample with reasonableDoubtExcluded := .unknown }
      = .unresolved := by decide

/-
CPP56 confession branch. The method must already have been assessed as falling
within this article's coercive illegal-method category, not any procedural defect.
-/
structure Confession56Input where
  evidenceId : String
  isSuspectOrDefendantConfession : Assessment
  qualifyingIllegalMethod : Assessment

def cpp56Confession (f : Confession56Input) : Trigger :=
  toTrigger (allAssessments [
    f.isSuspectOrDefendantConfession, f.qualifyingIllegalMethod])

theorem illegalConfessionTriggers :
    cpp56Confession ⟨"synthetic-e1", .established, .established⟩
      = .triggered := by decide

theorem uncertainMethodUnresolved :
    cpp56Confession ⟨"synthetic-e1", .established, .unknown⟩
      = .unresolved := by decide

inductive Remediation where
  | pending | cured | reasonablyExplained | neitherAvailable
  deriving DecidableEq, Repr

def neitherRemedyAvailable : Remediation → Assessment
  | .pending => .unknown
  | .cured => .refuted
  | .reasonablyExplained => .refuted
  | .neitherAvailable => .established

/-
All fields must refer to the same evidence. The record groups them by evidenceId;
it does not itself prove that externally supplied assessments are correctly bound.
-/
structure Material56Input where
  evidenceId : String
  isPhysicalOrDocumentary : Assessment
  unlawfulCollection : Assessment
  seriousJusticeRisk : Assessment
  remediation : Remediation

def cpp56Material (f : Material56Input) : Trigger :=
  toTrigger (allAssessments [
    f.isPhysicalOrDocumentary,
    f.unlawfulCollection,
    f.seriousJusticeRisk,
    neitherRemedyAvailable f.remediation])

def materialSample (r : Remediation) : Material56Input :=
  ⟨"synthetic-e2", .established, .established, .established, r⟩

theorem unremediableMaterialTriggers :
    cpp56Material (materialSample .neitherAvailable) = .triggered := by decide

theorem pendingRemediationUnresolved :
    cpp56Material (materialSample .pending) = .unresolved := by decide

theorem curedDoesNotTriggerThisBranch :
    cpp56Material (materialSample .cured) = .notTriggered := by decide

/-- Traceable outputs; missing snapshot hashes remain explicit. -/
structure Finding where
  source : SourceRef
  subjectId : String
  branchId : String
  result : Trigger

def cpp56Source : SourceRef :=
  { documentId := "PRC-CPP"
    versionId := "2018-amended"
    articleId := "56"
    officialUrl :=
      "https://www.samr.gov.cn/zw/zfxxgk/fdzdgknr/bgt/art/2025/art_48b3b0c3f954448e996602a71fc6f878.html"
    snapshotHash := none }

def cpp56MaterialFinding (f : Material56Input) : Finding :=
  { source := cpp56Source
    subjectId := f.evidenceId
    branchId := "physical-documentary-exclusion"
    result := cpp56Material f }

theorem findingPreservesSubject (f : Material56Input) :
    (cpp56MaterialFinding f).subjectId = f.evidenceId := by rfl

/-- Normative requirements and actual performance are separate. -/
structure EnforcementState where
  finding : Trigger
  exclusionPerformed : Bool

def exclusionRequired (w : EnforcementState) : Prop :=
  w.finding = .triggered

def exclusionOccurred (w : EnforcementState) : Prop :=
  w.exclusionPerformed = true

theorem noncompliancePossible :
    ∃ w : EnforcementState,
      exclusionRequired w ∧ ¬ exclusionOccurred w := by
  refine ⟨⟨.triggered, false⟩, ?_⟩
  decide

theorem obligationDoesNotGuaranteePerformance :
    ¬ (∀ w : EnforcementState, exclusionRequired w → exclusionOccurred w) := by
  intro h
  rcases noncompliancePossible with ⟨w, required, notOccurred⟩
  exact notOccurred (h w required)

#print axioms startIncluded
#print axioms endExcluded
#print axioms unknownNotRefuted
#print axioms assessmentNegationInvolutive
#print axioms confessionOnlyBarsConviction
#print axioms assessedEvidenceGatePasses
#print axioms unresolvedDoubtDoesNotPass
#print axioms illegalConfessionTriggers
#print axioms uncertainMethodUnresolved
#print axioms unremediableMaterialTriggers
#print axioms pendingRemediationUnresolved
#print axioms curedDoesNotTriggerThisBranch
#print axioms findingPreservesSubject
#print axioms noncompliancePossible
#print axioms obligationDoesNotGuaranteePerformance

end CriminalSystem

```

源码静态计数为238行、15个定理声明和15个公理依赖检查命令；这些命令尚未执行。合成案例与字段传递性质分别计数，不计作真实案件核验，也不能代替一般规则证明。刑诉法第55条其他内容、第56条证人证言和被害人陈述等分支及输入一致性检查仍未覆盖。

auditConjunction是冲突优先的保守审计聚合策略，不是通用逻辑合取。Finding保存来源声明，字段保留定理仅保证字段传递；它不证明原文真实性、事实绑定或适用效力。SourceRef中的snapshotHash为空表示官方原件快照待核；网页转载年份也不代表法律施行年份。[刑诉法官方转载正文](https://www.samr.gov.cn/zw/zfxxgk/fdzdgknr/bgt/art/2025/art_48b3b0c3f954448e996602a71fc6f878.html)。

# 全量接入顺序

1. 逐件完成859个版本记录的相关性分类，连接36个修改废止记录，并继续发现官方目录之外的必要刑事规范。目录快照的截止日期和检索口径必须固定。

2. 优先补120项已识别正文或版本缺口；取得相同标题但不同版本的材料不能自动消除缺口。正文摘要、下载失败或新闻解读不能替代规范原文。

3. 按“文书版本—条—款—项—分支”产生独立规则。原文结构节点和目录常量分别计数，不计入已证明规则数量。

4. 每条规则配置中文语义、带来源的形式模型及至少一个非空触发例；例外和数值边界另列反例，规则之间检查冲突和遗漏。

5. 通过独立法律复核后，再生成Lean声明；每章、每份解释设模块及对应案例文件，逐步接回原有505个刑法节点、308个刑诉节点和专题规则。

6. 固定工具链和依赖，运行干净构建、目标声明依赖检查及内核重放，保存日志和源码哈希，最后重新生成ctexart总稿、源码包和覆盖报告。

# 编译与证明验收

正式工程建议分为Source、Knowledge、Norm、CriminalLaw、Procedure、Interpretations、Cases和Audit模块。Source保存文书版本、条款定位和正文摘要；Norm保存规范模态、主体、阶段、例外和引用；案件事实作为显式输入，不声明为自定义法律公理。

验收同时检查实际定理的类型和传递依赖，禁止占位证明、额外法律公理及跳过内核检查的设置。#print axioms须针对最终目标逐个运行；标准逻辑公理可列允许名单，具体项目仍以构建输出为准。只有目录常量可编译，或只有同义展开的例子成立，不能算完整法律语义验证。[Lean官方证明验证说明](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)、[公理与依赖说明](https://lean-lang.org/doc/reference/latest/Axioms/)。

本轮执行环境配置失败，命令执行及文件写入工具均返回No usable execution environment。因此未读取现有本地源码、未安装或运行Lean、未执行构建、未生成新版PDF。本页保存的是可继续审查和执行的候选源码，而非已经通过内核的证明包。

# 本轮法源接入事项

以下是截至2026年10月27日本轮取得的接入证据，不构成全量目录已穷尽的结论。司法部新鉴别标准页面直接访问发生重定向循环，该项日期可由官方索引检得，但完整原文快照仍待验收。

| 规范或版本事项 | 已核到的时间与类型 | 接入要求 |
| --- | --- | --- |
| 刑诉法修改 | 最高法10月22日消息所列11月2日至6日常委会拟议程包括刑诉法修正草案 | 将拟审议草案与现行有效规则分开；该消息不能证明草案已经通过或施行 |
| 2026年修订监狱法 | 4月30日修订通过，11月1日施行；法律 | 同时保存当日适用的旧版与待施行新版，执行接口不得只以条号连接 |
| 暂予监外执行严重疾病范围和生活不能自理鉴别标准 | 司发通〔2026〕55号，9月24日署期，10月19日官网发布，11月1日施行；联合规范性文件 | 取得完整官方正文后核验替代关系，疾病、诊断、鉴别、批准分别建模 |
| 电磁动力枪支及散件认定会议纪要 | 8月27日署期，9月23日最高法发布；会议纪要 | 不标作司法解释，保留综合评估等限定，不能仅由单一参数推出犯罪成立 |
| 芬太尼类物质配套规范 | 《意见》法发〔2026〕12号与《立案追诉标准规定》为两个对象，9月23日施行 | 追诉门槛与定罪量刑分别建模，并保留药用分类、例外和主观明知 |
| 刑民交叉规定 | 法释〔2026〕19号，9月21日发布，9月22日施行；司法解释 | 分离刑民证明标准、程序中止条件及重复赔偿扣除规则 |

官方依据：[常委会会议安排](https://www.court.gov.cn/zixun/xiangqing/514981.html)、[2026年修订监狱法全文](https://www.spp.gov.cn/spp/zdgz/202604/t20260430_726743.shtml)、[司法部新鉴别标准索引](https://www.moj.gov.cn/pub/sfbgw/zwxxgk/fdzdgknr/fdzdgknrtzwj/202610/t20261019_540813.html)、[电磁动力枪支会议纪要](https://www.court.gov.cn/zixun/xiangqing/512681.html)、[芬太尼类物质意见](https://www.court.gov.cn/zixun/xiangqing/512701.html)、[芬太尼立案追诉标准官方转载](https://hzf.mofcom.gov.cn/article/zyfw/flfw/swflfggz/flfwbmgz/202609/8256.html)、[刑民交叉规定](https://www.court.gov.cn/zixun/xiangqing/512441.html)。

刑法和刑诉法的正式版本仍须以沿革及公布施行证据逐一核对，不能因网页发布时间较新便认为正文较新，也不能以检索未发现推定新修法绝不存在。

