import YM.Ground.Lean
import YM.Ground.Moments

/-!
# Proper pieces commute even before grid approximation
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS.Ground
open Function Set Filter Word Table
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff
variable {G : Gauge} {L : Register G} {S : Table L} {V : Chamber S timeAxis} (P : Spread V)
variable (H : Steady V) (Y : S.Hierarchy) (R : Rotation S) (h : R.Oriented S)

def orbit (K : Ortho) (x : Row.Core L) : Row.Core L := ⟨rotate x.val R K,(trans R Y h x.property K).1⟩

def world (K : Ortho) (x : Car L) : Car L := ⟨orbit Y R h K x.1,Ortho.move K ∘ x.2⟩
def stage (q : List (Row.Core L)) := inner ℂ V.omega0 ((starU P q).val V.omega0)

lemma whirl (q : List (Car L)) K (n) : all (q.map (world Y R h K)) n=rotate (all q n) R K := by
  have he (x : L.Word) t : carry (rotate x R K) (Ortho.move K t) = rotate (carry x t) R K := (rotated [] x R K t).symm
  induction q with
  | nil => rfl
  | cons x q ih =>
    rw [show all (_ :: q) n=carry x.1.val (x.2 n) ++ all q n from rfl]
    change carry (rotate _ R K) _ ++ all _ _=_
    rw [show ((world Y R h K x).2 n)=_ from rfl] -- ...
    rw [ih]
    change carry (rotate _ R K) (Ortho.move K (x.2 n)) ++ _ = _
    rw [he]; unfold rotate; rw [List.map_append]

include H
lemma alter (q v : List (Car L)) (hF : q.Perm v) (hQ : line q) K (hK : line (v.map (world Y R h K))) :
    stage P (q.map Prod.fst) = stage P ((v.map Prod.fst).map (orbit Y R h K)) := by
  let f := q.map Prod.fst
  let g := world Y R h K
  obtain ⟨hp,ht⟩ := arcs P H Y (v.map g) hK
  obtain ⟨hy,hs⟩ := arcs P H Y q hQ
  rw [show (List.map Prod.fst (v.map g))=(v.map Prod.fst).map (orbit Y R h K) by simp only [List.map_map];rfl] at ht
  apply tendsto_nhds_unique (f := fun i => S.expect (all q i)) hs (ht.congr' ?_)
  filter_upwards [hy] with i hi
  have he : List.Perm (all q i) (all v i) := (hF.map (fun x => carry _ _)).flatten
  rw [show all (v.map g) i=_ from whirl ..]; exact ((trans R Y h (locations.mpr ((he.map Prod.fst).nodup (locations.mp hi))) K).2).trans (Table.order S Y.laws.toSymmetric hi he)

lemma same_up (k : Ortho) (x : E4) (hX : 0 < x timeAxis) (hx : 0 < Ortho.move k x timeAxis) (q : List (Row.Core L)) :
    stage P q=stage P (q.map (orbit Y R h k)) := by
  let G (i : Fin q.length) : Car L := ⟨q.get i, fun n => (n:ℝ) • ((i.val:ℝ) • x)⟩
  let Q := List.ofFn G
  have he (v : E4) (h : 0<v timeAxis) (i j : Fin q.length) (hi : i<j) :
      flight (fun n => (n:ℝ) • ((i.val:ℝ) • v)) (fun n => (n:ℝ) • ((j.val:ℝ) • v)) := by
    have hp : 0 < ((j.val:ℝ)-i.val)*v timeAxis := mul_pos (sub_pos.mpr (by exact_mod_cast hi)) h
    refine Tendsto.congr (fun n => ?_) (Tendsto.atTop_mul_const hp tendsto_natCast_atTop_atTop)
    simp; ring
  have hh : line Q := List.pairwise_ofFn.mpr fun _ _ h => he _ hX _ _ h
  have hy (i) : (world Y R h k (G i)).2 = fun n : ℕ => (n:ℝ) • ((i.val:ℝ) • Ortho.move k x) := by
    funext n; change (Ortho.motion k) _ = _; rw [map_smul, map_smul];rfl
  have ht : line (Q.map _) := show line (Q.map (world Y R h k)) from
    List.pairwise_map.mpr (List.pairwise_ofFn.mpr fun i j h => by
      rw [hy i,hy j]; exact he _ hx _ _ h)
  have hv := alter P H Y R h Q Q (.refl _) hh k ht
  rw [show Q.map Prod.fst=q from by unfold Q; rw [List.map_ofFn]; exact List.ofFn_get ..] at hv; exact hv

-- need ONLY adjacent two middle of train of four
private def k : Signed := ⟨Equiv.swap timeAxis 0,fun _ => false⟩
omit H in
private lemma switch_ax (p : E4) : Ortho.move k.ortho p timeAxis=p 0 := by simp [Signed.ortho_move,k,Signed.act]

omit H in
private lemma boundOrder (w v : Car L) (t u : ℝ) (h : t<u) (hT : ∀ i, w.2 i timeAxis=i*t) (hU : ∀ i, v.2 i timeAxis=i*u) :
    flight w.2 v.2 := by
  simp_rw [flight,PiLp.sub_apply,hT,hU,← mul_sub]; exact Tendsto.atTop_mul_const (sub_pos.mpr h) tendsto_natCast_atTop_atTop
include Y R h in
lemma exchanges (x y w z : Row.Core L) : stage P [x,y,w,z]=stage P [x,w,y,z] := by
  have he (u v) : (u • basis timeAxis + v • basis 0) timeAxis=u ∧ Ortho.move k.ortho (u • basis timeAxis+v • basis 0) timeAxis=v := by simp [switch_ax] -- implicit u type
  let W (u v : ℝ) (q : Row.Core L) : Car L := ⟨q,fun i => (i:ℝ) • (u • basis timeAxis+v • basis 0)⟩
  have hx a b c d p q (h : a<b) : flight (W a c p).2 (W b d q).2 := boundOrder (W a c p) (W b d q) _ _ h (fun i => by simp [W]) (fun i => by simp [W])
  let V := world Y R h k.ortho
  have hy a b c d p q (h : c<d) : flight (V (W a c p)).2 (V (W b d q)).2 :=
    boundOrder _ _ _ _ h (fun i => by rw [show V (W a c p)=_ from rfl]; simp [W,V,world,switch_ax])
      (fun i => by simp [W,V,world,switch_ax])
  let A := W 0 0 x
  let B := W 1 2 y
  let C := W 2 1 w
  let D := W 3 3 z
  have hp : List.Perm [A,B,C,D] [A,C,B,D] := .cons _ (.swap ..)
  let ht := alter P H Y R h [A,B,C,D] [A,C,B,D] hp ?_ k.ortho ?_
  · refine ht.trans ?_
    let v := (1:ℝ) • basis timeAxis+(1:ℝ) • basis 0
    exact (same_up P H Y R h k.ortho v (show _ from (he 1 1).1 ▸ zero_lt_one) (show _ from (he 1 1).2 ▸ zero_lt_one) _).symm
  · simp [line]; refine ⟨⟨hx 0 1 0 2 _ _ (by norm_num),hx 0 2 0 1 _ _ (by norm_num),hx 0 3 0 3 _ _ (by norm_num)⟩,
          ⟨hx 1 2 2 1 _ _ (by norm_num),hx 1 3 2 3 _ _ (by norm_num)⟩, hx 2 3 1 3 _ _ (by norm_num)⟩
  simp [line]; refine ⟨⟨hy _ _ 0 1 _ _ (by norm_num),hy _ _ 0 2 _ _ (by norm_num),hy _ _ 0 3 _ _ (by norm_num)⟩,
     ⟨hy _ _ 1 2 _ _ (by norm_num),hy _ _ 1 3 _ _ (by norm_num)⟩, hy _ _ 2 3 _ _ (by norm_num)⟩
include Y R h
lemma gens (u v : Row.Core L) : Commute (M P u.val u.property) (M P v.val v.property) := by
  let A := starU P [u,v]
  let B := starU P [v,u]
  have he : DenseRange (V.D.orthogonalProjectionOnto ∘ V.GNS.stems) :=
    (show DenseRange _ from (show Surjective V.D.orthogonalProjectionOnto from
      fun p : V.D => ⟨_, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self p⟩).denseRange).comp V.GNS.whole V.D.orthogonalProjectionOnto.continuous
  have hz : (M P [] (locations.mpr (by simp))).val=ContinuousLinearMap.id ℂ _ := by
    have he := spots P H (vacuum_width (d := 1) (by norm_num))
    rw [he]; change P.atom _ _=_; unfold Spread.atom; rw [P.blank]; swap; norm_num
    ext1 x; change V.D.orthogonalProjectionOnto (V.flow.E _ x.val)=_
    rw [(V.flow.fixed _).1 x.property, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self];rfl
  have hf (i : Future L timeAxis) : (M P _ (twoSides i.property (air _).property)).val*1=(M P i.val i.property.1).val.adjoint := by
    rw [mul_one, slim P Y H, squeezed P H, ContinuousLinearMap.adjoint_comp,Submodule.adjoint_orthogonalProjectionOnto]
    have hw : X P (air _)= V.D.subtypeL := by
      have hv : Slab (L := L) timeAxis (1:ℝ≥0) [] := vacuum_width (by norm_num)
      rw [standing P _ hv]; change (P.place 1 []).comp _=_; rw [P.blank (by norm_num)]; ext1 x; exact (V.flow.fixed _).mp x.property _
    rw [hw]
  have hp (p : Voice L timeAxis) : A.val (V.D.orthogonalProjectionOnto (V.GNS.stems p))=
      B.val (V.D.orthogonalProjectionOnto (V.GNS.stems p)) := by
    induction p using Finsupp.induction_linear with
    | add p q hp hq => simp only [map_add,hp,hq]
    | zero => simp
    | single i c =>
      simp only [Kernel.Gram.stems,Finsupp.linearCombination_single,map_smul]
      congr 1
      apply he.eq_of_inner_right ℂ; intro f
      change inner ℂ (V.D.orthogonalProjectionOnto (V.GNS.stems f)) _= inner ℂ (V.D.orthogonalProjectionOnto (V.GNS.stems f)) _
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f p hf hp => simp only [map_add,inner_add_left,hf,hp]
      | single j s =>
        rw [← almost P H i]
        simp only [Kernel.Gram.stems,Finsupp.linearCombination_single, map_smul,inner_smul_left]
        rw [← almost P H j]
        rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.adjoint_inner_right ((M _ _ _).val), ← hf]
        have he := exchanges P H Y R h ⟨_,twoSides j.property (air _).property⟩ u v ⟨_,i.property.1⟩
        -- reassoc A& M
        simp only [A,B,stage,starU,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one] at he ⊢
        exact congr_arg (fun x : ℂ => star s*x) he
  have hh : A=B := Subtype.ext (DFunLike.coe_injective (he.equalizer A.val.continuous B.val.continuous (funext hp)))
  simp only [A,B,starU,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one] at hh
  exact hh

/-! Adjoints even without reflecting M_θ=M; `star` as operator carries θ/conj.
No assumption ordinary reality yet at M. -/
omit H R h in
lemma star_mem (x : V.VacuumOp) (hv : x∈P.generators) : star x∈P.generators := by
  obtain ⟨w,d,hv,rfl⟩ := hv
  refine ⟨opposite timeAxis d w,d,mirrorsSlab hv,?_⟩
  change ContinuousLinearMap.adjoint _=_; unfold Spread.atom
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp, P.adjoints hv Y.translations,
    Submodule.adjoint_subtypeL,Submodule.adjoint_orthogonalProjectionOnto]
  rfl

theorem adjunction : ∀ x y : P.algebra, x*y=y*x := by
  have hp (x y : V.VacuumOp) (hx : x∈ P.generators) (hy : y∈P.generators) : x*y=y*x := by
    obtain ⟨w,i,hx,rfl⟩ := hx
    obtain ⟨u,t,hy,rfl⟩ := hy
    have he := gens P H Y R h ⟨w,hx.2.1.1⟩ ⟨u,hy.2.1.1⟩
    change Commute (M P w _) (M P u _) at he
    rw [spots P H hx,spots P H hy] at he
    exact congr_arg Subtype.val he.eq
  let U := StarAlgebra.adjoin ℂ P.generators
  haveI : IsMulCommutative U := StarAlgebra.isMulCommutative_adjoin ℂ (fun _ hx _ hy => hp _ _ hx hy)
    (fun _ hx y hy => hp _ _ hx (star_mem P Y y hy))
  letI := U.commSemiringTopologicalClosure (fun x y => IsMulCommutative.is_comm.comm x y)
  exact fun (x y : U.topologicalClosure) => mul_comm x y
end YM.OS.Ground
