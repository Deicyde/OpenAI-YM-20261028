import YM.Next.MULTISOURCE.Formal
import YM.Next.MULTISOURCE.Packs


/-!
# Responses *at the unmarked density*

Formal squarefree coefficients of polarizations (no analyticity in an
unbounded-dimensional algebra assumed). Mixed response hypothesis later will
only use these at one adjacent-scale pair. It needn't produce densities at
some complex block parameter, nor a full perturbed path. Derive how to pay for
assembling perturbations from these, incl higher modes.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi
open Marker RG Wilson Lattice Finset
open scoped Topology BigOperators

variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W] [Fintype W] {R : Census V} {S : Census W}
variable {n : Side} {G : Gauge}

/-- Activity tangent at one fixed vacuum. Masks included in first entry.
Gas variations carry the Pack predicate (checked later in the cost). -/
abbrev Pulse (G : Gauge) (n : Side) :=
    (Config G n → ℂ) × (Pack n → Config G n → ℂ)

/-- Use THIS vacuum's flags and exponent. All modes in same polynomial. -/
def composeAt (P : Rep G n) (U : Config G n) (e : Poly R) (b : Pack n → Poly R) : Poly R :=
    (Real.exp (P.exponent U):ℂ) •
      (Poly.pass e * ∑ A∈ Pack.clears (flags P.p.threshold U), ∏ q∈A,
        (Poly.send R.quiet (incumbent P U q) + b q))

def lit (R : Census V) (a : Hot R → ℂ) : Poly R := ∑ T : Hot R, Poly.send T.val (a T)

def lambda (R : Census V) (a : V→ℂ) := ∑ i : V, Poly.send (R.fire i) (a i)

def many (P : Rep G n) (R : Census V) (D : Hot R → Pulse G n) (U : Config G n) : Poly R :=
    composeAt P U (lit R (fun i => (D i).1 U)) (fun A => lit R fun i => (D i).2 A U)

def polar (P : Rep G n) (R : Census V) (D : V → Pulse G n) (U : Config G n) : Poly R :=
    composeAt P U (lambda R fun i => (D i).1 U) (fun A => lambda R fun i => (D i).2 A U)

/-- Squarefree coefficient of the variation with first-order inputs only.
    In general NOT products of inserted cylinders. -/
def jet (P : Rep G n) (R : Census V) (D : V → Pulse G n) (T : R.Mode) (U : Config G n) :=
    (polar P R D U).part T

def shards (R : Census V) (T : R.Mode) := Finset.univ.filter (fun s : (parts R).Mode => unionOf s=T)
def blocksOf (R : Census V) (T : Hot R) := Finset.univ.filter (fun s : Hot (parts R) => unionOfHot s=T)

omit [Fintype V] in
lemma part_lit_quiet (a : Hot R → ℂ) : (lit R a).part R.quiet=0 := by
  rw [lit, Poly.part_sum]
  exact Finset.sum_eq_zero fun i _ => part_quiet_hot i _

omit [Fintype V] in
lemma part_lit (a : Hot R → ℂ) (v : Hot R) : (lit R a).part v.val = a v := by
  rw [lit,Poly.part_sum,sum_eq_single v]
  · simp
  · intro i _ hi
    rw [Poly.part_send,if_neg (show v.val≠i.val from fun h => hi (Subtype.ext h.symm))]
  simp

lemma lambda_quiet (a : V → ℂ) : (lambda R a).part R.quiet=0 := by
  rw [lambda,Poly.part_sum]; exact sum_eq_zero fun i _ => part_quiet_hot (Hot.one R i) _

lemma lambda_part (a : V → ℂ) (i : V) : (lambda R a).part (R.fire i)=a i := by
  rw [lambda,Poly.part_sum,sum_eq_single i]
  · simp
  · intro j _ h; simp [Ne.symm h]
  simp

lemma maps_at (F : Poly R →ₐ[ℂ] Poly S) (P : Rep G n) (U : Config G n) {e : Poly R} (b : Pack n → Poly R)
    (he : e.part R.quiet=0) (H : (F e).part S.quiet=0) :
    F (composeAt P U e b)=composeAt P U (F e) (fun i => F (b i)) := by
  have ha (x : ℂ) : F (Poly.send R.quiet x)=Poly.send S.quiet x := F.commutes x
  unfold composeAt
  simp only [map_smul, map_mul, map_prod, map_sum, map_add, ha, pass_map F e he H]

omit [Fintype V] in
lemma substitute_lit (a : Hot (parts R) → ℂ) :
    substitute R (lit (parts R) a)=lit R (fun x => ∑ i∈blocksOf R x,a i) := by
  have h (x : R.Mode) : (substitute R (lit (parts R) a)).part x =
      ∑ i : Hot (parts R), if x=unionOf i.val then a i else 0 := by
    simp_rw [lit, map_sum, substitute_apply,substituteL_send,Poly.part_sum,Poly.part_send]
  ext x; rw [h]
  by_cases H : x.val.Nonempty
  · let t : Hot R := ⟨x,H⟩
    have he (i : Hot (parts R)) : unionOfHot i=t ↔ x=unionOf i.val :=
      ⟨fun h => (congrArg Subtype.val h).symm, fun h => Subtype.ext h.symm⟩
    rw [← show t.val=x from rfl, part_lit, blocksOf,Finset.sum_filter]
    exact sum_congr rfl fun i _ => by simp only [show t.val=x from rfl, ← he]
  · have hx : x=R.quiet := Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp H)
    subst x
    rw [part_lit_quiet]; apply sum_eq_zero; intro i _
    rw [if_neg (show R.quiet ≠ unionOf i.val from fun h => H (by rw [h]; exact (unionOfHot i).property))]


omit [Fintype V] in
lemma substitute_lambda (a : Hot R → ℂ) : substitute R (lambda (parts R) a)=lit R a := by
  simp_rw [lambda, map_sum, substitute_apply, substituteL_send,unionOf_single]; rfl

omit [Fintype V] in
def foldRows (Z : Hot (parts R) → Pulse G n) (x : Hot R) : Pulse G n := ∑ i∈blocksOf R x, Z i

lemma fold_many (P : Rep G n) (Z : Hot (parts R) → Pulse G n) (U : Config G n) :
    substitute R (many P (parts R) Z U) = many P R (foldRows Z) U := by
  unfold many
  rw [maps_at _ _ _ _ (part_lit_quiet _) (by rw [substitute_lit,part_lit_quiet])]
  simp_rw [substitute_lit,foldRows]
  simp_rw [Prod.fst_sum,Prod.snd_sum,Finset.sum_apply]

lemma polar_many (P : Rep G n) (Z : Hot R → Pulse G n) (U : Config G n) :
    substitute R (polar P (parts R) Z U)=many P R Z U := by
  unfold many polar
  rw [maps_at _ _ _ _ (lambda_quiet _) (by rw [substitute_lambda,part_lit_quiet])]
  simp_rw [substitute_lambda]

omit [Fintype V] in
lemma substituted (a : Poly (parts R)) (T : R.Mode) :
    (substitute R a).part T = ∑ i∈shards R T,a.part i := by
  rw [substitute_apply,substituteL]; simp only [LinearMap.coe_mk, AddHom.coe_mk, Poly.part_sum]
  simp_rw [shards,Finset.sum_filter, Poly.part_send]; exact sum_congr rfl fun i _ => by simp only [eq_comm (a:=T)]

/-- All Bell partitions, no Bell number inserted. -/
lemma allJets (P : Rep G n) (Z : Hot R → Pulse G n) (U : Config G n) (T : R.Mode) :
    (many P R Z U).part T = ∑ i∈shards R T,jet P (parts R) Z i U := by
  rw [← polar_many P Z U]; exact substituted ..

omit [Fintype V] in
lemma dilation_lit (a : V → ℂ) (f : Hot R → ℂ) :
    dilation R a (lit R f) = lit R fun x => (∏ i ∈ x.sites,a i)*f x := by
  simp_rw [lit,map_sum,dilation_send]

lemma dilation_lambda (a : V → ℂ) (f : V → ℂ) : dilation R a (lambda R f) = lambda R fun x => a x*f x := by
  unfold lambda; rw [map_sum]; apply sum_congr rfl; intro i _; simp [dilation_send,Census.fire]

def ampl (a : V → ℂ) (D : Hot R → Pulse G n) (x : Hot R) : Pulse G n := (∏ i∈x.sites,a i) • D x

lemma amplify (P : Rep G n) (a : V → ℂ) (D : Hot R → Pulse G n) (U : Config G n) :
    dilation R a (many P R D U)=many P R (ampl a D) U := by
  unfold many
  rw [maps_at _ _ _ _ (part_lit_quiet _) (by rw [dilation_lit,part_lit_quiet])]
  simp_rw [dilation_lit]; rfl

lemma ampl_jet (P : Rep G n) (a : V → ℂ) (D : V → Pulse G n) (T : R.Mode) :
    jet P R (fun i => a i • D i) T = (∏ i∈T.val,a i) • jet P R D T := by
  have hf (U : Config G n) : dilation R a (polar P R D U)=polar P R (fun i => a i • D i) U := by
    unfold polar
    rw [maps_at _ _ _ _ (lambda_quiet _) (by rw [dilation_lambda,lambda_quiet])]
    simp_rw [dilation_lambda]; rfl
  funext U; simp only [jet, ← hf, dilation_part]; rfl

lemma jet_inputs (P : Rep G n) (D D' : V → Pulse G n) (T : R.Mode) (H : ∀ i∈T.val,D i=D' i) :
    jet P R D T=jet P R D' T := by
  let f (x : V) : ℂ := if x∈T.val then 1 else 0
  have he : ∀ D : V → Pulse G n, jet P R (fun i => f i • D i) T=jet P R D T := by
    intro D; rw [ampl_jet P f]
    rw [Finset.prod_eq_one (by intro i hi; exact if_pos hi), one_smul]
  have hs : (fun i => f i • D i)=fun i => f i • D' i := funext fun i => by
    by_cases h : i∈T.val
    · rw [H i h]
    simp only [f,h,↓reduceIte,zero_smul]
  exact (he D).symm.trans (by rw [hs, he])
end YM.Multi
