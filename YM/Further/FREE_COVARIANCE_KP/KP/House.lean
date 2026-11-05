import YM.Further.FREE_COVARIANCE_KP.KP.Alloy
import YM.Further.FREE_COVARIANCE_KP.KP.Cold


/-! # Cut multipliers of the endpoint tests. Smooth partition of
frequency on the enlarged cell, telescope checks for mesh later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex Matrix Work.F06 Exterior Precision Bloch Lattice Laurent
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {α Ω η : ℝ} {ι : Type*} {k l : ℤ}

def gate (x:ℝ) := Real.smoothTransition ((2*x)/Real.pi+5/2)
-- -1.25π to -.75π
def beam (x:ℝ) := gate x-gate (x-2*Real.pi)
def house (p:E4) : ℂ := ↑(∏ i, beam (p i))
def mural := 5*Real.pi/4
def facade : Set E4 := {p| ∀ i, |p i|≤mural}
lemma at_corner (x:ℝ) (hp : -3*Real.pi/4≤x) : gate x=1 := Real.smoothTransition.one_of_one_le (by have he := Real.pi_pos; field_simp; linarith)
lemma at_line (x:ℝ) (hp : x≤ -mural) : gate x=0 := Real.smoothTransition.zero_of_nonpos (by have he := Real.pi_pos; unfold mural at hp; field_simp; linarith)
lemma fearless : 1< mural ∧ mural<earth := by unfold mural earth; have he:=Real.one_le_pi_div_two; constructor <;> linarith
lemma closed_house : IsClosed facade := by
  rw [show facade=⋂ i:Axis, {p:E4 | |p i|≤mural} from by ext; simp [facade]]; exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
lemma beam_off (t : ℝ) (h : mural≤|t|) : beam t=0 := by
  unfold beam; have he := Real.pi_pos; rcases le_abs.mp h with h|h
  · unfold mural at h; rw [at_corner _ (by linarith),at_corner _ (by linarith)]; norm_num
  · rw [at_line _ (by linarith),at_line _ (by linarith)]; norm_num
lemma house_off (p : E4) (h : p∉facade) : house p=0 := by
  obtain ⟨i,hi⟩ := not_forall.mp h; rw [house,Finset.prod_eq_zero (Finset.mem_univ i) (beam_off _ (le_of_not_ge hi)),Complex.ofReal_zero]
lemma house_core : house 0=1 := by
  have he := Real.pi_pos
  simp [house,beam,at_corner 0 (by linarith),at_line (- (2*Real.pi)) (by unfold mural; linarith)]
lemma house_smooth : ContDiff ℝ ∞ house := by
  have h : ContDiff ℝ ∞ (fun p:E4 => ∏ i, beam (p i)) := by unfold beam gate; fun_prop
  exact Complex.ofRealCLM.contDiff.comp h

def veranda : Window where
  look := facadeᶜ
  ok := closed_house.isOpen_compl
  hole H := H (fun i => by simpa using zero_le_one.trans fearless.1.le)
lemma stroll (p:E4) (h : p∈whole) : p∈search ∨ p∈veranda := by
  by_cases hp:p∈facade; exact Or.inl ⟨fun i=> (hp i).trans_lt fearless.2,h⟩; exact Or.inr hp
lemma away_bounds : veranda.look ⊆ (rim 1 zero_lt_one).look := by
  intro p hp; obtain ⟨i,h⟩ := not_forall.mp hp; have he := abs_real_inner_le_norm (basis i) p
  simp only [basis_inner,basis_norm,one_mul] at he; exact (fearless.1.trans (lt_of_not_ge h)).trans_le he
lemma blend {ι : Type*} {f : ι → E4 → ℂ} {u v w : Window} (ht : Weight u k f) (hk : Weight v k f) (H : ∀ p:E4, p∈w → p∈u ∨ p∈v) : Weight w k f := by
  refine ⟨fun i p hp => ?_,fun n => ?_⟩
  · rcases H _ hp with hx|hx
    exact ((ht.smooth i).contDiffAt (u.ok.mem_nhds hx)).contDiffWithinAt
    exact ((hk.smooth i).contDiffAt (v.ok.mem_nhds hx)).contDiffWithinAt
  obtain ⟨A,hA,ha⟩ := ht.quotes n; obtain ⟨B,hB,hb⟩ := hk.quotes n
  refine ⟨A+B,by positivity,fun i p hp => ?_⟩
  rcases H _ hp with hx|hx; apply (ha i p hx).trans; gcongr; linarith
  apply (hb i p hx).trans; gcongr; linarith

def bill (s : E4→Axis→ℂ) (A : List Axis) (p:E4) := (A.map (s p)).prod
def record (A B : List Axis) (f : Firm α Ω η) (p:E4) := (bill tooth A p) • (star (bill tooth B p) • garnet f p)
def pearls (A B : List Axis) (p:E4) := (bill turned A p) • (star (bill turned B p) • pearl p)
def rebus (A B : List Axis) (f : Firm α Ω η) (p:E4) := house p • record A B f p
/-- Full error versus continuized low symbol including the derivatives. -/
def ivory (A B : List Axis) (f : Firm α Ω η) (p:E4) := rebus A B f p-breeze 1 p • pearls A B p

def sizeL (A : List Axis) : ℤ := A.length
lemma do_bill (A : List Axis) {u : E4 → Axis → ℂ} {s} (h : ∀ i, Weight (ι:=ι) s 1 (fun _ p=> u p i)) : Weight (ι:=ι) s (sizeL A) (fun _ p=> bill u A p) := by
  induction A with
  | nil => simpa [sizeL,bill] using (Weight.spare (ι:=ι) s 1)
  | cons i A ih => simpa [bill,sizeL,add_comm] using (h i).times ih
lemma f_bill (A : List Axis) : Weight (ι:=ι) search (sizeL A) (fun _ p=> bill tooth A p) := do_bill A (fun i => (tooth_go i).1)
lemma g_bill (A : List Axis) : Weight (ι:=ι) whole (sizeL A) (fun _ p=> bill turned A p) := do_bill A turn_price
lemma diff_bill (A : List Axis) : Weight (ι:=ι) search (sizeL A+1) (fun _ p=> bill tooth A p-bill turned A p) := by
  induction A with
  | nil => simpa [sizeL,bill] using (Weight.vanish (ι:=ι) search 1)
  | cons i A ih =>
    have ht := ((tooth_go (ι:=ι) i).1).times ih
    have he := ((tooth_go (ι:=ι) i).2).times ((g_bill A).use rake_subset)
    rw [show 1+(sizeL A+1)=sizeL (i::A)+1 by simp [sizeL]; omega] at ht
    rw [show 2+sizeL A=sizeL (i::A)+1 by simp [sizeL]; omega] at he
    apply (ht.sum he).stay; intro _ p hp; simp only [bill,List.map_cons,List.prod_cons]; ring

lemma charged_pearls (A B : List Axis) : Value whole (sizeL A+sizeL B) (fun (_:ι) => pearls A B) := by
  let O := (1:Matrix X1 X1 ℂ)
  have h : Value whole 1 (fun (_:ι) p => wedge 1 (turned p)) := laid _ turn_price
  have hg : Value whole (-2) (fun (_:ι) p => (spine p)⁻¹ • O) := Value.priced reciprocal_high (show Value whole 0 (fun (_:ι) (_:E4)=>O) from fun i j => Weight.spare _ _)
  have hh : Value whole 0 (fun (_:ι)=>pearl) := (h.product hg).product h.starM
  have he := Value.priced (g_bill A) (Value.priced (g_bill B).conjugated hh); rw [add_zero] at he; exact he

lemma times_help {U : Window} {f g : ArrayM ι X2 X2} {s t : ι→ E4 → ℂ} (h : Weight U k s) (hh : Weight U (k+1) (fun i p => s i p-t i p))
    (he : Value U l g) (hg : Value U (l+1) (fun i p=> f i p-g i p)) : Value U (k+l+1) (fun i p=>s i p • f i p - t i p • g i p) := by
  have ht := Value.priced hh he; have hd := Value.priced h hg
  rw [add_right_comm] at ht; rw [← add_assoc] at hd
  apply (hd.joint ht).switched; intro i p hp; dsimp only; rw [smul_sub,sub_smul]; abel
lemma record_pay (A B : List Axis) (ha : 0<α) (he : 0<η) : bask (record A B (Ω:=Ω) (α:=α) (η:=η)) (sizeL A+sizeL B) ∧ bask (fun (f : Firm α Ω η) p => record A B f p-pearls A B p) (sizeL A+sizeL B+1) := by
  let I := Firm α Ω η
  obtain ⟨hj,ht⟩ := gem_quote ha (Ω:=Ω) he
  constructor
  · have hh := Value.priced (f_bill A) (Value.priced (f_bill B).conjugated (show Value _ _ _ from hj)); rw [add_zero] at hh; exact hh
  have hg : Value search 0 (fun (_:I) => pearl) := fun i j => by
    have hh := charged_pearls (ι:=I) [] [] i j |>.use rake_subset
    simpa [pearls,bill,sizeL] using hh
  have hB : Weight search (sizeL B+1) (fun (_:I) p => star (bill tooth B p)-star (bill turned B p)) := by
    simpa only [star_sub] using (diff_bill (ι:=I) B).conjugated
  have he := times_help (f_bill B).conjugated hB hg ht
  have hh := times_help (f_bill A) (diff_bill A) (Value.priced (((g_bill B).use rake_subset).conjugated) hg) he; rw [add_zero] at hh; exact hh
lemma win_house : Weight (ι:=ι) search 0 (fun _ => house) := (Plain.sample _ house_smooth).zero_power (by positivity [earth_pos]) search_short
lemma veranda_free (A B : List Axis) : Value veranda k (rebus A B (α:=α) (Ω:=Ω) (η:=η)) := fun i j =>
  (Weight.vanish _ _).stay fun a p hp => by simp [rebus,house_off p hp]
lemma house_pay (A B : List Axis) (ha : 0<α) (hb : 0<η) : Value whole (sizeL A+sizeL B) (rebus A B (α:=α) (Ω:=Ω) (η:=η)) := by
  have he := Value.priced win_house (show Value _ _ _ from (record_pay A B ha (Ω:=Ω) hb).1)
  rw [zero_add] at he
  exact fun i j => blend (he i j) (veranda_free A B i j) stroll
lemma ivory_lives (A B : List Axis) : Value veranda k (ivory A B (α:=α) (Ω:=Ω) (η:=η)) := by
  let I := Firm α Ω η
  let r := sizeL A+sizeL B
  have ht : Weight (ι:=I) veranda (k-r) (fun _ => breeze 1) := (far_fee _ (le_refl 1) zero_lt_one zero_lt_one).use away_bounds
  have hg : Value veranda r (fun (_:I) => pearls A B) := fun i j => (charged_pearls A B i j).use fun x hx => veranda.out hx
  have h := Value.priced ht hg; rw [sub_add_cancel] at h; exact Value.remove (veranda_free A B) h
lemma ivory_goes (A B : List Axis) (ha : 0<α) (hb : 0<η) : Value whole (sizeL A+sizeL B+1) (ivory A B (α:=α) (Ω:=Ω) (η:=η)) := by
  let I := Firm α Ω η
  have H : Weight (ι:=I) search 1 (fun _ p=> house p-breeze 1 p) := (Plain.sample _ (house_smooth.sub (breeze_smooth _))).one_power (by positivity [earth_pos]) search_short fun i=> by simp [house_core,breeze,polar]
  have h := times_help win_house H (show Value search _ _ from fun i j => (charged_pearls (ι:=I) A B i j).use rake_subset) (show Value _ _ _ from (record_pay A B ha hb).2)
  rw [zero_add] at h; exact fun i j => blend (h i j) (ivory_lives A B i j) stroll
end YM.Further.FreeCovariance.KP
