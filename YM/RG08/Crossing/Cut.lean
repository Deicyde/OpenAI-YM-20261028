import YM.RG08.Crossing.Flats
/-! # Linear carry through the kinetic probe, preserve one pre gain. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Conductor
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary
open scoped BigOperators Topology Real Classical
variable {G : Gauge} (i : G.ColorIndex) (Q : Pot G 2) (r : ℕ)

def penny (r : ℕ) : Pot G (r+2) → Pot G (r+2) := match r with
 | 0 => sifting i Q
 | _+1=> id
lemma penny_add {F H : Pot G (r+2)} (h : Glows F)(p : Glows H): penny i Q _ (F+H)=penny i Q _ F+penny i Q _ H := by cases r; exact sifting_add i Q h p; rfl
lemma penny_sub {F H : Pot G (r+2)} (h : Glows F)(p : Glows H): penny i Q _ (F-H)=penny i Q _ F-penny i Q _ H := by cases r; exact sifting_sub i Q h p; rfl
lemma penny_fee {C A B : ℝ} (h : Glow Q B C)(hp : 0<B){F : Pot G (r+2)}(he : Glow F B A) : Glow (penny i Q r F) B ((1+probeFee G B*C)*A) := by
  cases r; exact sifting_height i _ he h hp
  apply glow_less he le_rfl
  exact le_mul_of_one_le_left he.nonneg (le_add_of_nonneg_right (mul_nonneg (probe_fee ..) h.nonneg))
variable {I : Type} {y δ w : I→ℝ} {Q V : I → Pot G 2} {r : ℕ} {F H : I→Pot G (r+2)}
lemma penny_paid (h : Audience y) (hh : ∀ j,0<w j)(hu : Weighed y (fun j=>probeFee G (w j)))(hp : Voucher y 1 Q w)(he : Voucher y δ F w) : Voucher y δ (fun j=> penny i (Q j) r (F j)) w := by
  obtain ⟨A,hA,H⟩:=hp; obtain ⟨C,hC,H'⟩:=he; refine ⟨_,(Weighed.plus Weighed.one (hu.times hA) h).times hC,fun j=>?_⟩
  rw [Pi.mul_apply,mul_assoc]; refine glow_less (penny_fee i _ _ (H j) (hh j) (H' j)) le_rfl ?_
  simp only [Pi.one_apply,mul_one,Pi.add_apply,Pi.mul_apply,le_refl]
lemma penny_both (h : Audience y) (hh : ∀ j,0<w j)(hu : Weighed y (fun j=>probeFee G (w j)))(hp : Both y δ Q V w)(he : Both y δ F H w) :
    Both y δ (fun j=> penny i (Q j) r (F j)) (fun j=>penny i (V j) r (H j)) w := by
  cases r; exact paired_cut i h hh hu hp he; exact he
lemma penny_gain {B : ℝ} {X : Chain} {N j : ℕ} {K : KPrices X.kernel} {g : KGate K} {P : Lending G X.kernel} {E : ℕ} (S : Prism G X.kernel g P E)
    {F : Pot G (r+2)} (hp : Glow F (Tier S j) ((B/Real.sqrt (X.S.block j).val)/share G (Tier S j) (K.bill (X.J j)))) :
    Glow (penny i (Chain.column G X N j) r F) (Tier S j) (B*gain X.S (1/2) j (j+1)) := by
  apply glow_less (penny_fee i _ _ (Q_loans S N j) (S.positive _) hp) le_rfl
  let A:=share G (Tier S j) (K.bill (X.J j)); have hh:0<A:= zero_lt_one.trans_le (share_one G (Tier S j) (K.solvent _))
  rw [gain_succ_half, mul_one_div]; exact (mul_div_cancel₀ _ hh.ne').le
end YM.RG08.Conductor
