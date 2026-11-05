import YM.Next.FREE_KERNELS.Curl

/-!
# Divisibility on real principal cube

Factor *all* one-step filters needed on the nonprincipal alias at once.
Used before the coefficient width argument. Only continuity of the local
factor is consumed, so no Need for costing a Cauchy division on a patch
whose formulas have poles. Ψ convention (unmodified metrics).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid
open scoped Topology BigOperators ComplexConjugate
variable {α β ι : Type*} {j t : ℕ}

lemma Pay.cooled {w : ι → ℝ} {f : ι → Momentum → Matrix α β ℂ} (h : Pay w f) (i : ι) {p : Momentum} (hp : p∈baseCube) : ContinuousAt (f i) p := by
  change ContinuousAt (fun p a b => f i p a b) p; refine continuousAt_pi.mpr fun a => continuousAt_pi.mpr fun b => ?_
  obtain ⟨η,C,hη,hC,h⟩ := h.tap a b
  exact ((h i).hol p (mem_cube_real (base_subset_realCube hη hp) hη)).continuousAt

def scarf (L : Side) (q : Momentum) (a : Axis) :=
    ((L.val:ℂ)⁻¹*twirl (q a) (-mid L))*(∏ i∈Finset.univ.erase a, plank L (q i))
def scaffold (L : Side) (q : Momentum) (s : List Axis) := (s.map (scarf L q)).prod

lemma scarf_rule (P : Flight j t) (q : Momentum) (l : Site P.L) (a : Axis) :
    chip (aliasAt q l a)*area P.L (aliasAt q l)=chip (q a)*scarf P.L (aliasAt q l) a := by
  unfold area scarf
  let x := aliasAt q l a
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)];
  have hh := hinges_rule P l q a
  simp only [tripQ,(by simp : ((↑((1:Side).val)):ℂ)=1),one_mul] at hh
  rw [← hh]; conv_lhs => rw [show plank P.L (aliasAt q l a)=_ from Eq.refl (twirl (aliasAt q l a) (-mid P.L)*rail P.L (aliasAt q l a))]
  have he := side_ne P.L; field_simp

lemma scaffold_rule (P : Flight j t) (p : Momentum) (l : Site P.L) (s : List Axis) :
    listChip (aliasAt p l) s*area P.L (aliasAt p l) ^ s.length = listChip p s * scaffold P.L (aliasAt p l) s := by
  induction s with
  | nil => simp [listChip,scaffold]
  | cons a s ih =>
    simp only [listChip,List.map_cons,List.prod_cons,List.length_cons,pow_succ,scaffold];
    let q := aliasAt p l
    change (chip _ * listChip q s) * _ = (_ * listChip p s)* (_ * scaffold _ q s)
    rw [show chip (q a)*listChip q s*(area P.L q ^ s.length*area P.L q)=chip (q a)*area P.L q*(listChip q s * area P.L q ^ s.length) by ring];
    unfold q; rw [scarf_rule,ih]; ring
lemma scaffold_ready (L : Side) (s : List Axis) : Continuous fun p : Momentum => scaffold L p s := by
  have h (a : Axis) : Continuous (fun p : Momentum => scarf L p a) := by unfold scarf plank rail twirl; fun_prop
  induction s with
  | nil => exact continuous_const
  | cons a s ih => exact (h a).mul ih

namespace Flight

def shallow (P : Flight j t) (r : ℕ) (p : Momentum) := mask r (fun i => rail P.L ((-p) i))
def priorStake (k : ℝ) (P : Flight j t) (p : Momentum) (l : Site P.L) :=
    let q := aliasAt p l
    pulse k P.wing q * signal P.L 1 q * mask 1 (P.portD k p l)* P.shallow 1 q * mirage 1 1 p +
    P.levy k p l • (P.shallow 2 q * P.notch k p)
lemma lifted_high (P : Flight j t) (p : Momentum) (l : Site P.L) (k : ℝ) (hl : l≠0) :
    P.wire k p l=area P.L (aliasAt p l)^j • P.priorStake k p l := by
  let q := aliasAt p l
  have hf (r : ℕ) : flux P r q=area P.L q ^ j • P.shallow r q := by
    unfold flux hinges; rw [Matrix.transpose_smul,mask_trans,massFilter_even]; rfl
  unfold wire; rw [if_neg hl]; unfold stake priorStake
  simp only []; rw [hf 1,hf 2]; simp only [Matrix.smul_mul,Matrix.mul_smul,smul_add]; rw [smul_comm]

def fasten (P : Flight j t) (p : Momentum) (a : Axis) := ((P.L.val:ℂ)*rail P.L (P.toe p a))⁻¹
def material (P : Flight j t) (p : Momentum) (s : List Axis) := (s.map (P.fasten p)).prod
lemma fasten_nonzero (P : Flight j t) {p : Momentum} (hp : p∈baseCube) (a) :
    (P.L.val:ℂ)*rail P.L (P.toe p a)≠0 := by
  let L := P.L
  apply mul_ne_zero (side_ne P.L)
  unfold toe; rw [alias_zero_eq]; apply norm_pos_iff.mp (plankMin_pos.trans_le (rail_lower P.L _ _))
  rw [narrow_apply, norm_div, Complex.norm_natCast, mul_div_cancel₀ _ (side_pos P.L).ne']
  exact zone_in_disk _ (mem_cube_real (base_subset_realCube zone_pos hp) zone_pos) _
lemma fasten_rule (P : Flight j t) {p : Momentum} (hp : p∈baseCube) (a) :
    chip (P.toe p a)=chip (p a)*P.fasten p a := by
  have he := hinges_rule P 0 p a
  simp only [tripQ,(by simp : ((↑((1:Side).val)):ℂ)=1),one_mul] at he
  have hh := P.fasten_nonzero hp a
  change rail P.L (P.toe p a)*_=chip _ at he
  unfold fasten; rw [← he];
  -- divisibility cancellation
  change chip (P.toe p a)=rail P.L (P.toe p a)*((P.L.val:ℂ)*chip (P.toe p a))*_
  generalize hx : rail P.L (P.toe p a)=b at *; have h1 : b≠0 := right_ne_zero_of_mul hh; have h2 := side_ne P.L; field_simp
lemma material_rule (P : Flight j t) {p : Momentum} (hp : p∈baseCube) (s : List Axis) :
    listChip (P.toe p) s=listChip p s*material P p s := by
  induction s with
  | nil => simp [listChip,material]
  | cons a s ih => change chip _*listChip (P.toe p) s=(chip (p a)*listChip p s)*(P.fasten p a*material _ p s); rw [ih,fasten_rule P hp]; ring
lemma material_ready (P : Flight j t) {p : Momentum} (hp : p∈baseCube) (s : List Axis) : ContinuousAt (fun p => P.material p s) p := by
  have hh (a : Axis) : ContinuousAt (fun p => P.fasten p a) p := by
    have hm : ContinuousAt (fun p => (P.L.val:ℂ)*rail P.L (P.toe p a)) p := by unfold rail toe aliasAt twirl; fun_prop
    exact hm.inv₀ (fasten_nonzero P hp a)
  induction s with
  | nil => exact continuousAt_const
  | cons a s ih => exact (hh a).mul ih

/-- Ψ using the same period independent unmodified stencil. -/
def alloy (k : ℝ) (P : Flight j t) (p : Momentum) (l : Site P.L) := agile k P p l*pulse k P.land p

variable (k : ℝ) (hk : 0<k) (hj : 4≤j) (ht : 4 ≤ t)
include hk hj ht
lemma status_quote : Secured (alloy (j:=j) (t:=t) k) := by
  have hm := agility k hk hj ht
  have hG := (heart_budget k hk ht (fun i : Σ P : Flight j t, Site P.L => i.1.land)).1
  have he := hm.pay.times hG; simp only [mul_one] at he
  refine ⟨he,fun P p hp x hx l => ?_,fun P p hp l => ?_⟩
  · unfold alloy; rw [hm.relay _ _ hp x hx l,(overlap_heart k hk _ hp x hx).1]
  unfold alloy; rw [shade_mul, hm.pearl _ _ hp, shade_pulse _ hk _ hp]

omit hj
/-- Merely regular, no claimed pre-L cost. -/
lemma high_cont (P : Flight j t) {p : Momentum} (hp : p∈baseCube) (l : Site P.L) (hl : l≠0) : ContinuousAt (fun p => P.priorStake k p l) p := by
  let i := Unit
  let F (_ : Unit) := P
  let L (_ : Unit) := l
  have hm := Pay.expose_mask 1 (fun a => portD_budget k P.legal F L (fun _ => hl) (fun _ => a))
  have hV := (heart_budget k hk P.legal (fun _ : Unit => P.wing)).1.on_alias (fun _=>P.L) (fun _=>P.odd) L
  have hS (r : ℕ) : Pay (fun _ : Unit => (1:ℝ)^r) fun (_ : Unit) p => P.shallow r (aliasAt p l) := by
    exact Pay.expose_mask _ (fun a => reverse_rails F L (fun _ => a))
  have hh := ((((hV.times (sig_budget F L 1)).times hm).times (hS 1)).times (out_budget (ι:=Unit) 1).reverse.transpose).cooled () hp
  have hg := (((hS 2).times (notch_budget k hk ht F)).scale (levy_budget k hk P.legal ht F L fun _ => hl)).cooled () hp
  unfold priorStake; exact hh.add hg

lemma cable_exists (P : Flight j t) (s : List Axis) (hs : s.length≤j) :
    ∀ l : Site P.L, ∃ g : Momentum → Frequency 2 2, (∀ p∈baseCube, ContinuousAt g p) ∧ ∀ p∈baseCube,
      listChip (aliasAt p l) s • alloy k P p l=listChip p s • g p := by
  intro l; by_cases h : l=0
  · subst l
    refine ⟨fun p => P.material p s • P.alloy k p 0, ?_,fun p hp => ?_⟩
    · intro p hp
      have he := (status_quote k hk P.legal ht).pay.cooled (⟨P,0⟩ : Σ P : Flight j t, Site P.L) hp
      exact (P.material_ready hp s).smul he
    rw [P.material_rule hp, smul_smul]
  let q := fun p => aliasAt p l
  let w := fun p => vault k P.wing (q p)*P.priorStake k p l*pulse k P.land p
  let y := fun p => area P.L (q p)^(j-s.length)*scaffold P.L (q p) s
  refine ⟨fun p => y p • w p, ?_,fun p hp => ?_⟩
  · intro p hp
    have hc : Continuous q := by unfold q aliasAt; fun_prop
    have he := (heart_budget k hk P.legal (fun _ : Unit => P.wing)).2.cooled () (alias_base hp l P.odd)
    have hh := (heart_budget k hk ht (fun _ : Unit => P.land)).1.cooled () hp
    have hg : Continuous y := ((Train.area_diff _).continuous.comp hc).pow _ |>.mul ((scaffold_ready _ _).comp hc)
    exact hg.continuousAt.smul (((he.comp (f:=q) hc.continuousAt).mul (high_cont k hk ht P hp l h)).mul hh)
  change _=listChip p s • (y p • w p); unfold alloy agile; rw [P.lifted_high p l k h]; simp only [Matrix.mul_smul,Matrix.smul_mul,smul_smul]
  have he := scaffold_rule P p l s
  unfold w y q
  congr 1
  have hh (x : ℂ) : x^j=x^s.length*x^(j-s.length) := by rw [← pow_add,Nat.add_sub_of_le hs]
  rw [hh,← mul_assoc, he]; ring
end Flight
end YM.Next.Free
