import YM.Extra.ITERATION_NO_LOSS.Columns
import YM.Work.B17
import YM.Work.G04

/-!
# Coarse terms from a fine curvature tensor through its first nonzero degree

Whole-path placement and quantitative absolute bounds. Shift through true
residues; when the input is a two-difference pattern, we require a separate
zero-fiber receipt for the used columns in checking the output loop jets.
No identification of higher nonlinear jets by linear curl substitution here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Placement
open Lattice Wilson RG Exterior Precision Bloch Matrix Laurent Finset Work.F08 Function
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {L c f : Side} {G : Gauge} {ι : Type*} {k : ℕ}

abbrev Columns (L : Side) := Option Axis → Cross L (TypeFace 2) (TypeFace 2)
abbrev Address (k : ℕ) := (Fin k → PlaqAxes) × (Fin k → Cover)

def entry (ψ : Columns L) (a : Pattern G k) (r : Site L) (b : Fin k → PlaqAxes) (i : Fin k) :=
    let s := a.atom.leg i
    ψ (a.op i) (arrives r s.offset,plaquette s.plaq) (plaquette (b i))

def reach (a : Pattern G k) (r : Site L) (y : Fin k → Cover) i := carry r (a.atom.leg i).offset + y i

def term (ψ : Columns L) (a : Pattern G k) (r : Site L) (z : Address k) :=
    relocate a.atom (∏ i, entry ψ a r z.1 i (z.2 i)) (reach a r z.2) z.1

lemma term_symm (ψ : Columns L) (a : Pattern G k) (r z) (ha : a.atom.Invariant) :
    (term ψ a r z).Invariant := relocated_symm a.atom ha _ _ _

private lemma length_weight (ψ : Columns L) (a : Pattern G k) (r z) {η σ : ℝ} (he : 0 ≤ η) (hs : η ≤ σ*L.val) :
    η * (term ψ a r z).length ≤ σ * a.atom.length + 8*η*k + ∑ i, η*Laurent.size (z.2 i) := by
  have hL := side_pos L
  have hσ : 0 ≤ σ := nonneg_of_mul_nonneg_left (he.trans hs) hL
  rw [term,relocated_length,Nat.cast_add,Nat.cast_sum,mul_add]; push_cast
  unfold Atom.length; rw [Nat.cast_sum, mul_sum,mul_sum]; unfold reach
  have hi (i : Fin k) : (η* (Laurent.size (carry r (a.atom.leg i).offset + z.2 i):ℝ)) ≤
      σ*(a.atom.leg i).length + 4*η + η * Laurent.size (z.2 i) := by
    have hx := offset_size (a.atom.leg i)
    have hf : (Laurent.size (a.atom.leg i).offset:ℝ) ≤ (a.atom.leg i).length := by
      exact_mod_cast hx.trans (Nat.le_add_right _ 4)
    calc
      _ ≤ η * ((Laurent.size (carry r (a.atom.leg i).offset) : ℝ) + Laurent.size (z.2 i)) := by
        gcongr; exact_mod_cast Laurent.size_add _ _
      _ ≤ η * ((Laurent.size (a.atom.leg i).offset / (L.val:ℝ)+4) + Laurent.size (z.2 i)) := by gcongr; exact carry_bound ..
      _ = (η/L.val) * Laurent.size (a.atom.leg i).offset + 4*η + η * Laurent.size (z.2 i) := by ring
      _ ≤ _ := by gcongr; exact (div_le_iff₀ hL).2 hs
  have hl := sum_le_sum fun i (_:i∈univ) => hi i
  rw [sum_add_distrib,sum_add_distrib,sum_const,card_univ,Fintype.card_fin, nsmul_eq_mul] at hl
  linarith

def wallet (η : ℝ) (k : ℕ) (A : ℝ) := Real.exp (8*η*k)*(Fintype.card PlaqAxes:ℝ)^k*A^k
lemma wallet_nonneg (η k) {A : ℝ} (hA : 0 ≤ A) : 0 ≤ wallet η k A := by unfold wallet; positivity

lemma term_price {ψ : Columns L} (a : Pattern G k) (r : Site L) {A η σ : ℝ} (hA : 0 ≤ A)
    (he : 0 ≤ η) (hs : η ≤ σ*L.val) (h : ∀ i, (ψ (a.op i)).strip η A) :
    SumBudget (fun z => (term ψ a r z).budget η) (wallet η k A * a.atom.budget σ) := by
  let u := Real.exp (8*η*k) * a.atom.budget σ
  have hu : 0 ≤ u := by unfold u Atom.budget Atom.magnitude; positivity
  have hw (b : Fin k → PlaqAxes) : SumBudget (fun y : Fin k → Cover => (term ψ a r (b,y)).budget η) (u*A^k) := by
    have ht := Cost.pi (fun i => h i (arrives r (a.atom.leg i).offset,plaquette (a.atom.leg i).plaq) (plaquette (b i)))
    rw [prod_const,card_univ,Fintype.card_fin] at ht
    refine Cost.mono (Cost.scale ht u hu) (fun i => by unfold Atom.budget Atom.magnitude; positivity) ?_
    intro y
    simp_rw [prod_mul_distrib, ← Real.exp_sum, Real.norm_eq_abs,show ∀ i, ψ (a.op i) (arrives r (a.atom.leg i).offset, plaquette (a.atom.leg i).plaq)
      (plaquette (b i)) = entry ψ a r b i from fun _ => rfl, ← Finset.abs_prod]
    have hm : (term ψ a r (b,y)).magnitude = |∏ i,entry ψ a r b i (y i)| * a.atom.magnitude := relocated_coeff ..
    unfold u Atom.budget; rw [hm]
    have hp := Real.exp_monotone (length_weight ψ a r (b,y) he hs)
    rw [Real.exp_add,Real.exp_add] at hp
    refine (mul_le_mul_of_nonneg_left hp (by unfold Atom.magnitude; positivity : (0:ℝ) ≤ |∏ i, entry ψ a r b i (y i)| * a.atom.magnitude)).trans_eq ?_
    ring
  have hx := Cost.product (F:=fun z => (term ψ a r z).budget η) (Cost.finite (α:=Fin k → PlaqAxes) (u*A^k) (by positivity)) hw
  convert hx using 1
  unfold wallet u; rw [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]; ring

def book (ψ : Columns L) (E : ι → Pattern G k) (p : ι × Site L × Address k) := term ψ (E p.1) p.2.1 p.2.2

lemma book_symm (ψ : Columns L) (E : ι → Pattern G k) (h : ∀ i, (E i).atom.Invariant) : SymmetricAtoms (book ψ E) :=
  fun p => term_symm ψ (E p.1) _ _ (h p.1)

lemma book_price {ψ : Columns L} (E : ι → Pattern G k) {A C η σ : ℝ} (hA : 0 ≤ A)
    (he : 0 ≤ η) (hs : η ≤ σ*L.val) (q : ℕ) (hq : 4 ≤ q*k)
    (h : ∀ p i, (ψ ((E p).op i)).strip η (A/(L.val:ℝ)^q)) (hE : Charged (fun i => (E i).atom) σ C) :
    Charged (book ψ E) η (wallet η k A / (L.val:ℝ)^(q*k-4) * C) := by
  have hL := side_pos L
  let v := wallet η k (A/(L.val:ℝ)^q)
  have hv : 0 ≤ v := wallet_nonneg _ _ (by positivity)
  have hv' : (L.val:ℝ)^4 * v = wallet η k A / (L.val:ℝ)^(q*k-4) := by
    have hm : (L.val:ℝ)^ (q*k) = (L.val:ℝ)^(q*k-4)*L.val^(4:ℕ) := by rw [← pow_add, Nat.sub_add_cancel hq]
    unfold v wallet; rw [div_pow,← pow_mul,hm]; field_simp
  have hx (i : ι) : SumBudget (fun p : Site L × Address k => (book ψ E (i,p)).budget η)
      ((L.val:ℝ)^4*v*((E i).atom.budget σ)) := by
    rw [mul_assoc]
    have ho := Cost.finite (α:=Site L) (v*((E i).atom.budget σ)) (by unfold Atom.budget Atom.magnitude; positivity)
    rw [site_card,Nat.cast_pow] at ho
    exact Cost.product ho (fun r => term_price (E i) r (A:=A/(L.val:ℝ)^q) (by positivity) he hs (h i))
  rw [Charged,← hv']; exact Cost.product (Cost.scale hE ((L.val:ℝ)^4*v) (by positivity)) hx

/-- Exact linear-flux equality; counts all colors in `entry` products. -/
def Substitution (g : Ratio c f) (ψ : Columns g.count) (F : Flux G f) (V : Flux G c) := ∀ i b j x,
    Iteration.read i (F b j) x = ∑ p : PlaqAxes, ∑' y, ψ i (g.residue x,plaquette b) (plaquette p) y * V p j (g.parent x+wrap c y)

section transport
variable {g : Ratio c f} {ψ : Columns g.count} {F : Flux G f} {V : Flux G c} (hd : Substitution g ψ F V)
    (a : Pattern G k) (r : Site g.count) (x : Site c) {η σ A : ℝ} (he : 0 < η) (hA : 0 ≤ A) (h : ∀ i, (ψ (a.op i)).strip η A)

private def value (ψ : Columns L) (V : Flux G c) (a : Pattern G k) (r : Site L) (x : Site c)
    (d : Fin k → G.ColorIndex) (b : Fin k → PlaqAxes) (i : Fin k) (y : Cover) :=
    entry ψ a r b i y * V (b i) (d i) (x+wrap c (carry r (a.atom.leg i).offset+y))

include he h in
private lemma value_abs (d b i) : Summable (fun y => |value ψ V a r x d b i y|) := by
  have hv y : |V (b i) (d i) y| ≤ ∑ v,|V (b i) (d i) v| := single_le_sum (f:=fun v => |V (b i) (d i) v|)
    (fun _ _ => abs_nonneg _) (mem_univ y)
  unfold value; simp_rw [abs_mul]; exact ((Row.rights _ _ (h i) he.le _ (plaquette (b i))).mul_right _).of_nonneg_of_le
    (fun _ => by positivity) (fun y => mul_le_mul_of_nonneg_left (hv _) (abs_nonneg (entry ψ a r b i y)))

include he hA h hd in
private lemma expanded (z : Site f) (e : z = g.assemble (x,r)) : a.sample F z = ∑' u : Address k,
    (plain (term ψ a r u)).sample V x := by
  subst z
  let P := value ψ V a r x
  have hi (d : Fin k → G.ColorIndex) (i : Fin k) : Iteration.read (a.op i) (F (a.atom.leg i).plaq (d i))
      (g.assemble (x,r) + wrap f (a.atom.leg i).offset) = ∑ b : PlaqAxes, ∑' y, P d (fun _ => b) i y := by
    rw [hd]; simp_rw [moves_parent,moves_residue,Ratio.assemble_res,Ratio.assemble_parent,P,value,map_add,← add_assoc]; rfl
  have hp d b := Cost.tsum_pi (fun i => value_abs (V:=V) a r x he h d b i)
  have hT : Charged (term ψ a r) η _ := term_price a r hA he.le (show η ≤ η*g.count.val by
    exact le_mul_of_one_le_right he.le (by exact_mod_cast g.count.pos)) h
  have hs := sample_summable (plain ∘ term ψ a r) V he.le hT x
  change _ = ∑' u, ((plain ∘ term ψ a r) u).sample V x
  rw [hs.tsum_prod,tsum_fintype]; conv_lhs => simp only [Pattern.sample,hi,Fintype.prod_sum]
  have hpart (b d) : Summable (fun y : Fin k → Cover => a.atom.coeff d * ∏ i, P d b i (y i)) := (hp d b).1.of_abs.mul_left _
  have hx b y : (plain (term ψ a r (b,y))).sample V x = ∑ d, a.atom.coeff d * ∏ i,P d b i (y i) := by
    unfold Pattern.sample plain term relocate; simp only [slot_plaq,slot_offset, Iteration.read,Option.elim,reach,P,value]
    simp only [prod_mul_distrib]; apply sum_congr rfl; intros; ring
  change _ = ∑ b, ∑' y, (plain (term ψ a r (b,y))).sample V x
  simp_rw [hx,Summable.tsum_finsetSum (fun d _ => hpart _ d),tsum_mul_left]; rw [Finset.sum_comm]; apply sum_congr rfl
  intro d _; rw [mul_sum]; apply sum_congr rfl; intro b _; congr 1; exact (hp d b).2.symm

include he hd hA
lemma book_eq (E : ι → Pattern G k) (hψ : ∀ u i, (ψ ((E u).op i)).strip η A)
    (hbook : Summable (fun u : ι × Site g.count × Address k => ∑ y, (plain (book ψ E u)).sample V y)) :
    total (plain ∘ book ψ E) V = total E F := by
  unfold total; rw [show ∑' e, ∑ x : Site c, ((plain ∘ book ψ E) e).sample V x = _ from hbook.tsum_prod]
  apply tsum_congr; intro u
  rw [(hbook.prod_factor u).tsum_prod, tsum_fintype, ← Equiv.sum_comp g.splitSites.symm (fun z => (E u).sample F z),
    Fintype.sum_prod_type, Finset.sum_comm (s:=univ) (f:=fun x r => (E u).sample F _)]
  refine sum_congr rfl fun r _ => ?_
  have hT : Charged (term ψ (E u) r) η _ := term_price (E u) r hA he.le (show η ≤ η*g.count.val by
    exact le_mul_of_one_le_right he.le (by exact_mod_cast g.count.pos)) (hψ u)
  change (∑' i, ∑ x, ((plain ∘ term ψ (E u) r) i).sample V x) = _
  rw [Summable.tsum_finsetSum (fun x _ => sample_summable (plain ∘ term ψ (E u) r) V he.le hT x)]
  exact sum_congr rfl fun x _ => (expanded hd (E u) r x he hA (hψ u) _ rfl).symm
end transport


lemma component_abs (x : Cover) (l : Axis) : |(x l:ℝ)| ≤ Laurent.size x := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]; exact_mod_cast Finset.single_le_sum (fun i _ => Nat.zero_le ((x i).natAbs)) (mem_univ l)

lemma moments_summable {a : ι → Atom G 2} {σ C : ℝ} (hs : 0 < σ) (h : Charged a σ C) (i b) :
    Summable (fun p => charge (a p) i b) ∧ ∀ l : Axis, Summable (fun p => charge (a p) i b * delta (a p) l) := by
  have hb := h.absolute hs.le
  have hc (p) : |charge (a p) i b| ≤ (a p).magnitude := by unfold charge; split; exact coeff_le ..; simp [Atom.magnitude,sum_nonneg]
  refine ⟨Summable.of_norm_bounded hb hc,fun l => ?_⟩
  have hm := (h.moments 1 hs).2.1; simp only [pow_one,sub_self,Atom.budget,zero_mul,Real.exp_zero,mul_one] at hm
  refine Summable.of_norm_bounded hm fun p => ?_
  rw [norm_mul,mul_comm,Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul ((component_abs ..).trans (le_trans (by exact_mod_cast delta_size (a p))
    (le_add_of_nonneg_left zero_le_one))) (hc p) (abs_nonneg _) (by positivity)

private lemma width_moment {f : Cover → ℝ} {η A : ℝ} (he : 0 < η) (h : Width η A f) (z : Cover) (l : Axis) :
    Summable (fun x => |f x * (z+x) l|) := by
  have hz : Summable (fun y : Cover => |f y * y l|) := by
    refine (h.2.1.mul_left (momentPrice 1 η)).of_nonneg_of_le (fun _ => abs_nonneg _) ?_
    intro y; rw [← mul_assoc, abs_mul,mul_comm,Real.norm_eq_abs]; apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    have he := spendMoment 1 he (Nat.cast_nonneg (Laurent.size y))
    rw [pow_one] at he
    exact (component_abs y l).trans (by linarith : (Laurent.size y : ℝ) ≤ momentPrice 1 η * Real.exp (η * Laurent.size y))
  simp_rw [Pi.add_apply, Int.cast_add,mul_add]; exact (((h.unweighted he.le).2.1.mul_right |(z l:ℝ)|).add hz).of_nonneg_of_le
    (fun _ => abs_nonneg _) fun y => (abs_add_le ..).trans (by rw [abs_mul, Real.norm_eq_abs])

lemma term_silent (a : Pattern G 2) (r : Site L) (b : Fin 2 → PlaqAxes) (hu : both a) {η A : ℝ} {ψ : Columns L}
    (he : 0 < η) (hs : ∀ i,(ψ (a.op i)).strip η A) (hz : Cancels ψ) : Silent fun y : Fin 2 → Cover => term ψ a r (b,y) := by
  intro i d
  let f := entry ψ a r b
  let z (j : Fin 2) := carry r (a.atom.leg j).offset
  have hp (j : Fin 2) : (∑' x, f j x) = 0 := by
    obtain ⟨w,h⟩ := Option.isSome_iff_exists.mp (hu j)
    change (∑' x, ψ (a.op j) _ _ x) = _
    rw [h]; exact (hz ..).tsum_eq
  have habs (j : Fin 2) : Summable fun y => |f j y| := Row.rights _ _ (hs j) he.le _ _
  let u := if b=i then a.atom.coeff d else 0
  have hv (y) : charge (term ψ a r (b,y)) i d = u * ∏ j, f j (y j) := by
    change (if (fun j => b j) = i then _ else 0)=_
    dsimp only [term,relocate]; unfold u f; split <;> simp [mul_comm]
  simp_rw [hv]
  have hm := Cost.tsum_pi habs
  constructor
  · have h := hm.1.of_abs.hasSum.mul_left u
    rw [hm.2] at h; simpa only [hp, Fin.prod_univ_two,mul_zero] using h
  intro l
  let g j x := f j x * (z j+x) l
  have hcost (j) : Summable fun x => |g j x| := width_moment he (hs ..) ..
  have hh (j : Fin 2) : HasSum (fun y : Fin 2 → Cover => (∏ i, f i (y i)) * (((z j + y j) l:ℤ):ℝ)) 0 := by
    let H (i : Fin 2) := if i=j then g i else f i
    have hb := Cost.tsum_pi (f:=H) (fun i => by unfold H; split; exact hcost i; exact habs i)
    have heq : (fun y : Fin 2 → Cover => (∏ i, f i (y i)) * (((z j + y j) l:ℤ):ℝ)) = fun y => ∏ i, H i (y i) := by
      funext y; fin_cases j <;> simp [H,Fin.prod_univ_two, g] <;> ring
    rw [heq]; convert! hb.1.of_abs.hasSum using 1; rw [hb.2,Fin.prod_univ_two]; fin_cases j <;> simp [H,hp]
  have hl := ((hh 1).sub (hh 0)).mul_left u
  simp_rw [delta,term,relocate,slot_offset, Pi.sub_apply,Int.cast_sub,reach]
  convert! hl using 1
  · funext y; unfold z; ring
  simp

lemma book_silent (E : ι → Pattern G 2) (hu : ∀ p,both (E p)) {η A C : ℝ} {ψ : Columns L}
    (he : 0 < η) (hs : ∀ p i,(ψ ((E p).op i)).strip η A) (hz : Cancels ψ) (h : Charged (book ψ E) η C) :
    Silent (book ψ E) := by
  intro i b
  have hb := moments_summable he h i b
  have heq (f : ι × Site L × Address 2 → ℝ) (hf : Summable f)
      (hq : ∀ p r k, HasSum (fun y => f (p,r,k,y)) 0) : HasSum f 0 := by
    convert! hf.hasSum using 1; rw [hf.tsum_prod]; simp_rw [(hf.prod_factor _).tsum_prod,
      ((hf.prod_factor _).prod_factor _).tsum_prod,(hq ..).tsum_eq]; simp
  have h p r k := term_silent (E p) r k (hu p) he (hs p) hz i b
  exact ⟨heq _ hb.1 (fun p r k => (h p r k).1),fun l => heq _ (hb.2 l) (fun p r k => (h p r k).2 l)⟩
end YM.Extra.Iteration.Placement
