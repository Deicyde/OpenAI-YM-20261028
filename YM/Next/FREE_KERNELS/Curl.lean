import YM.Next.FREE_KERNELS.Lifts
import YM.Next.FREE_KERNELS.Primal
import YM.Work.F08.Mixed

/-!
# The fine closed cost in a step

Apply one *fine* difference before the right exterior lift, retaining its
extra power of L. Transfer operators still *installed*; coverage of nonzero
momenta alone is not used to infer period identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08
open scoped Topology BigOperators ComplexConjugate

variable {m n ι : Type*}

lemma crank_cost (r : ℕ) (s : Axis) (i j) : ‖left ℝ r s i j‖ ≤ 1 := by unfold Exterior.left; rw [Matrix.of_apply]; split_ifs <;> simp [parity]
lemma carry_crank (L : Side) (ho : Odd L.val) (s : Axis) (i : Site L) : carry i (step s)=carryStep s i := by
  have he := carry_spec i (step s)
  rw [← cover_step ho s i, arrives,map_add,wrap_lift,wrap_step] at he
  ext a
  have hm := congr_fun (add_left_cancel he) a
  simp at hm; exact hm.symm
lemma stays_here {L : Side} (x : Site L) : carry x 0=0 := by
  have hh := carry_spec x 0
  rw [arrives,add_zero,wrap_lift] at hh
  ext a
  have hm := congr_fun hh a; simp [nsmul_eq_mul] at hm; simpa

lemma curl_layout {L : Side} (ho : Odd L.val) (r : ℕ) (f : Cross L (TypeFace r) m) (i b p) :
    fineCompose (cobound r) f i b p=∑ a : TypeFace r, ∑ s, left ℝ r s i.2 a*forwardC L f s (i.1,a) b p := by
  unfold fineCompose; refine Finset.sum_congr rfl fun j _ => ?_
  let A (x : Cover) := f (arrives i.1 x,j) b (p-carry i.1 x)
  unfold routed; rw [tsum_eq_sum (s:=support)]; swap
  · exact fun a ha => by rw [certified r i.2 j a ha]; simp
  unfold cobound; simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _ => ?_
  have hh : step a ∈ support := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
  have hz : (0:Cover)∈support := Finset.mem_insert_self ..
  simp only [mul_sub,sub_mul,mul_ite,ite_mul,mul_one,mul_zero,zero_mul,Finset.sum_sub_distrib,Finset.sum_ite_eq',if_pos hh,if_pos hz]
  rw [stays_here,carry_crank _ ho,← mul_sub]; unfold arrives forwardC; simp only [map_add,wrap_lift,wrap_step,add_zero,sub_zero]; rfl
lemma curl_quote {L : Side} (ho : Odd L.val) (r : ℕ) (f : Cross L (TypeFace r) m) {η C : ℝ}
    (hp : 0≤C) (h : ∀ s, (forwardC L f s).strip η C) :
    (fineCompose (cobound r) f).strip η (Fintype.card (TypeFace r) * (Fintype.card Axis*C)) := by
  intro i j; simp_rw [show fineCompose (cobound r) f i j=(fun p => ∑ a : TypeFace r, ∑ s, left ℝ r s i.2 a*forwardC L f s (i.1,a) j p) from funext (curl_layout ho r f i j)]
  apply width_sum_finite
  intro a; apply width_sum_finite; intro s
  exact (Width.scale_line _ (h s (i.1,a) j)).mono le_rfl (mul_le_of_le_one_left hp (crank_cost ..))

variable {j t : ℕ}
/-- Standard names for unmodified bed coordinates. -/
def pink (k : ℝ) (v : Train j) := record (pulse k v)
def blue (k : ℝ) (v : Train j) := record (vault k v)
lemma heart_saves {ι : Type*} (k : ℝ) (hk : 0<k) (hj : 4≤j) (v : ι → Train j) :
    Stock (α:=fun _ => TypeFace 2) (β:=fun _ => TypeFace 2) (fun _ : ι => 1) (fun i => pink k (v i)) ∧
    Stock (α:=fun _ => TypeFace 2) (β:=fun _ => TypeFace 2) (fun _ : ι => 1) (fun i => blue k (v i)) := by
  obtain ⟨σ,C,hσ,hC,h⟩ := heart_banked k hk hj v
  constructor <;> refine ⟨fun _ => zero_le_one,σ,C,hσ,hC,fun i => ?_⟩ <;> rw [mul_one]
  · exact (h i).1
  exact (h i).2
lemma heart_inverse (k : ℝ) (hk : 0<k) (hj : 4≤j) (v : Train j) (c : Side) :
    (pink k v).acts c*(blue k v).acts c=1 ∧
      ((pink k v).acts c)ᵀ=(pink k v).acts c ∧ ((blue k v).acts c)ᵀ=(blue k v).acts c := by
  let w (_ : Unit) := v
  have hb := heart_saves k hk hj w
  obtain ⟨hh,hg⟩ := heart_true k hk hj v
  let A := pink k v; let B := blue k v
  have hA : Whole A := hb.1.whole ()
  have hB : Whole B := hb.2.whole ()
  constructor
  · let R := unitRow (TypeFace 2)
    change A.acts c*B.acts c=1
    rw [← hA.acts hB,← acts_unit (n:=c)]
    apply Whole.eq_on (hA.prod hB) (Whole.coin _)
    intro p hp; rw [hA.read hB hp.1,read_unit,show A.read p=_ from hh.echo p hp,show B.read p=_ from hg.echo p hp]
    exact (pulse_pays k hk _ (base_subset_realCube zone_pos hp)).1
  change (A.acts c)ᵀ=A.acts c ∧ (B.acts c)ᵀ=B.acts c
  rw [← acts_trans,← acts_trans]; refine ⟨Whole.eq_on hA.flipped hA ?_ c,Whole.eq_on hB.flipped hB ?_ c⟩ <;> intro p hp <;> rw [read_opposite _ hp.1]
  · rw [show A.read p=_ from hh.echo _ hp]; exact (heart_Herm k hk v (base_subset_realCube zone_pos hp)).1
  rw [show B.read p=_ from hg.echo _ hp]; exact (heart_Herm k hk v (base_subset_realCube zone_pos hp)).2

namespace Flight

def agile (k : ℝ) (P : Flight j t) (p : Momentum) (l : Site P.L) := vault k P.wing (aliasAt p l)*wire k P p l
def buckle (k : ℝ) (P : Flight j t) := meshBook (agile k) 2 [] P
def curlStep (k : ℝ) (P : Flight j t) := fineCompose (cobound 2) (buckle k P)
def charge (k : ℝ) (P : Flight j t) := composeRows (curlStep k P) (pink k P.land)
def sale (k : ℝ) (P : Flight j t) := capLift 1 (charge k P)

abbrev fee (e : ℕ) (P : Flight j t) := ((P.L.val:ℝ)^e)⁻¹

section costs
variable (k : ℝ) (hk : 0<k) (hj : 4≤j) (ht : 4≤t)
include hk hj ht
lemma agility : Secured (agile (j:=j) (t:=t) k) := by
  have H := (secure_both k hk hj ht).2
  let I := Σ P : Flight j t,Site P.L
  have he := (heart_budget k hk hj (fun x : I => x.1.wing)).2.on_alias (fun x => x.1.L) (fun x => x.1.odd) fun x => x.2
  have hh := he.times H.pay
  simp only [one_mul] at hh
  refine ⟨hh,fun P p hp x hx l => ?_,fun P p hp l => ?_⟩
  · unfold agile; rw [H.relay P p hp x hx l]
    obtain ⟨a,ha⟩ := alias_exchange p l x
    have hf := alias_in_real zone_pos hx l P.odd; rw [ha] at hf
    rw [ha, (overlap_heart k hk _ (alias_in_real zone_pos hp _ P.odd) _ hf).2]
  have hc := alias_in_real zone_pos hp l P.odd
  unfold agile; rw [shade_mul,H.pearl P p hp,alias_reverse p P.odd]
  have hy := (heart_real k hk P.wing (realCube_neg hc)).2
  rw [neg_neg] at hy; rw [shade,hy]

abbrev Transaction (w : ℕ) (f : ∀ P : Flight j t, Cross P.L m n) := Stock (α:=fun P => Co P.L m) (β:=fun _ => n) (fee w) f

lemma budgets_linear : Transaction (m:=TypeFace 2) (n:=TypeFace 2) 2 (buckle (j:=j) (t:=t) k) ∧
    Transaction (m:=TypeFace 2) (n:=TypeFace 2) 2 (fun P : Flight j t => (duo k P).T) := by
  have he (W : Thread j t (TypeFace 2) (TypeFace 2)) (h : Secured W) : Transaction (m:=TypeFace 2) (n:=TypeFace 2) 2 (fun P => meshBook W 2 [] P) := by
    obtain ⟨σ,C,hσ,hC,h⟩ := h.bankCost hj 2 (u:=[]) (Nat.zero_le _)
    refine ⟨fun i => by unfold fee; positivity,σ,C,hσ,hC,fun i => ?_⟩
    simpa only [fee,div_eq_mul_inv,List.length_nil,Nat.add_zero] using h i
  exact ⟨he _ (agility k hk hj ht),he _ (secure_both k hk hj ht).2⟩
lemma budget_curl : Transaction (m:=TypeFace 3) (n:=TypeFace 2) 3 (curlStep (j:=j) (t:=t) k) := by
  obtain ⟨σ,C,hp,hC,h⟩ := Secured.honored (agility k hk hj ht) hj 2
  let B := (Fintype.card (TypeFace 2):ℝ); let D := (Fintype.card Axis:ℝ)
  have hB : 0≤B := by unfold B; positivity; -- price slack added
  have hD : 0≤D := by unfold D; positivity
  refine ⟨fun i => by unfold fee; positivity,σ,B*D*C+1,hp,by positivity,fun P => ?_⟩
  let u := fee 3 P
  have hm : 0 ≤ u := by unfold u fee; positivity
  have hh (a : Axis) : (Precision.forwardC P.L (buckle k P) a).strip σ (C*u) := by
    have he := h P [a] (show 1≤j-2 by omega); rw [div_eq_mul_inv] at he; exact he
  apply strip_mono (curl_quote P.odd 2 _ (mul_nonneg hC.le hm) hh) le_rfl
  change B*(D*(C*u)) ≤ (B*D*C+1)*u; linarith
lemma budget_charge : Transaction (m:=TypeFace 3) (n:=TypeFace 2) 3 (charge (j:=j) (t:=t) k) := by
  have hh := Stock.times (budget_curl k hk hj ht) (heart_saves k hk ht (fun P : Flight j t => P.land)).1
  unfold Transaction charge; simpa only [mul_one] using hh
lemma budget_sale : Transaction (m:=TypeFace 3) (n:=TypeFace 3) 3 (sale (j:=j) (t:=t) k) := folded_stock (r:=1) (budget_charge k hk hj ht) (List.finRange 4)
end costs
end Flight
end YM.Next.Free
