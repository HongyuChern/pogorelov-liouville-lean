import CHSComparator.MathlibOnly.Bridge
import CHS.PaperTargets

namespace CHSComparator.MathlibOnly.Targets

theorem theorem_1_1 : Statements.theorem_1_1 :=
  Bridge.theorem_1_1_iff.mpr @CHS.Paper.theorem_1_1

theorem theorem_1_2 : Statements.theorem_1_2 :=
  Bridge.theorem_1_2_iff.mpr @CHS.Paper.theorem_1_2

theorem theorem_1_3 : Statements.theorem_1_3 :=
  Bridge.theorem_1_3_iff.mpr @CHS.Paper.theorem_1_3

theorem corollary_1_4 : Statements.corollary_1_4 :=
  Bridge.corollary_1_4_iff.mpr @CHS.Paper.corollary_1_4

end CHSComparator.MathlibOnly.Targets
