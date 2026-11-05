import YM.RG08.Carrel.Cost
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # If a diagram sum is received polynomially at every fixed field evaluation, this lemma
     exchanges the summation also after g-polynomial shifts on those variables (even mixed
     transforms depending on parameters or other fields). Without assuming summable cost of
     true germ remainders.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Aggregate
open Forms Steam Cloud Camera Glyph Room Carrel Filter MvPolynomial Finset Function
open scoped Topology PowerSeries BigOperators Classical
variable {I J K:Type}{n e:ℕ}
variable [Fintype I]

def parlin (n:ℕ)(I:Type)[Fintype I]:Flake n I→ₗ[ℝ] Inn I where
 toFun:=parley
 map_add':=parley_add
 map_smul':=parley_smul

abbrev Lane (I:Type)[Fintype I](n:ℕ):=LinearMap.range (parlin n I)
instance :FiniteDimensional ℝ (Lane I n):=Module.Finite.range (parlin n I)
lemma lane_in (p:Flake n I): parley p∈Lane I n:=LinearMap.mem_range_self _ _
lemma lane_photograph (f:Still I):tap n (flask f)∈Lane I n:=by rw [flute,←deck_parley f]; apply lane_in

def street (I:Type)(x:I→ℝ):Inn I →ₗ[ℝ] ℝ:=(MvPolynomial.aeval x).toLinearMap
 omit [Fintype I] in
lemma meter (f:Inn I)(x:I→ℝ): street I x f=MvPolynomial.eval x f:=rfl

lemma Lane.full (L: Module.Dual ℝ ↥(Lane I n)):L ∈ Submodule.span ℝ (Set.range (fun x:I→ℝ=> (street I x).comp (Lane I n).subtype)):=by
 let Q:=Submodule.span ℝ (Set.range (fun x:I→ℝ=> (street I x).comp (Lane I n).subtype))
 change L∈Q; rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W:=Q)]
 apply (Submodule.mem_dualAnnihilator _).2;intro y hy
 unfold Q at hy; rw [←SetLike.mem_coe,Submodule.coe_dualCoannihilator_span] at hy
 have he(x:I→ℝ): MvPolynomial.eval x y.val=0:=hy ((street I x).comp (Lane I n).subtype) ⟨x,rfl⟩
 have hf:y=0:=by apply Subtype.ext; exact MvPolynomial.funext (fun x=>by rw [he]; exact (map_zero _).symm)
 rw [hf,map_zero]

/-- Condition consuming path & translation analytic weights (or any receipt meeting same). -/
def Along (J:Type){I:Type}(p:J→Inn I)(q:Inn I):Prop:=∀ x:I→ℝ,HasSum (fun j=> MvPolynomial.eval x (p j)) (MvPolynomial.eval x q)
lemma Along.extrapolate {p:J→Inn I}{q:Inn I}(h:Along J p q)(hp:∀ j,p j∈Lane I n)(hq:q∈Lane I n)(L:Inn I→ₗ[ℝ]ℝ): HasSum (fun j=> L (p j)) (L q):=by
 let r:=Lane I n
 let t (i:J):r:= ⟨p i,hp i⟩
 let b:r:=⟨q,hq⟩
 let f(L:Module.Dual ℝ r)(_h:L ∈ Submodule.span ℝ (Set.range (fun x:I→ℝ=> (street I x).comp (Lane I n).subtype))) := HasSum (fun j=>L (t j)) (L b)
 change f (L.comp r.subtype) (Lane.full (L.comp r.subtype))
 exact Submodule.span_induction (p:=f) (by rintro _ ⟨x,rfl⟩;exact h x) (hasSum_zero) (fun a b _ _ ha hb=>ha.add hb) (fun a x _ hh=>hh.const_smul a) (Lane.full _)

-- pull into larger or even just evaluation alphabet J

def screening (x:I→Port J)(a:J→ℝ)(i:ℕ):Inn I→ₗ[ℝ] ℝ:= (street J a).comp (((PowerSeries.coeff i).restrictScalars ℝ).comp (Room.lug x).toLinearMap)
lemma Along.shard {F:K→Inn I}{q:Inn I}(h:Along K F q)(hp:∀ i,F i∈Lane I n)(hq:q∈Lane I n)(x:I→Port J)(i:ℕ)(a:J→ℝ):HasSum (fun j=> MvPolynomial.eval a (tap i (Room.lug x (F j)))) (MvPolynomial.eval a (tap i (Room.lug x q))) := h.extrapolate hp hq (screening x a i)

-- transfer multiple coupling orders together, each has chosen degree.
lemma sweep {F:K→Port I}{q:Port I}(m:ℕ→ℕ)(e:ℕ)(h:∀ i≤e,Along K (fun k=>tap i (F k)) (tap i q))
    (hp:∀ i≤e,∀ k,tap i (F k)∈Lane I (m i)) (hq:∀ i≤e,tap i q∈Lane I (m i))(x:I→Port J): Along K (fun k=>tap e (belt x (F k))) (tap e (belt x q)):=by
 intro a
 change HasSum (fun k=> MvPolynomial.eval a (tap e (spool (lug _) _))) (MvPolynomial.eval a (tap e (spool (lug _) _))) -- `_` functions
 simp_rw [ships,map_sum]
 exact hasSum_sum (fun i hi=> (h _ (by simpa using hi)).shard (hp _ (by simpa using hi)) (hq _ (by simpa using hi)) x (e-i) a)
end YM.RG08.Aggregate
