import YM.RG08.Camera.Rack

/-!
# Produce Room change condition from Taylor invoices and smooth Haar chart costs
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Camera
open Glyph Cloud Room Room.Haze MvPolynomial Finset Filter Function Matrix
open scoped ContDiff Topology BigOperators PowerSeries Classical
variable {I A B R T:Type}[Fintype I][Fintype A][Fintype B][Fintype R][Fintype T]
namespace Rail
variable {Γ γ:Matrix I I ℝ}{hΓ:∀ i j,Γ i j=Γ j i}{hγ:∀ i j,γ i j=γ j i}
variable {H: Ledger (Raw I A) R}{S:Ledger (Raw I B) T}(q:Rail I A B)

structure Base (H:Ledger (Raw I A) R)(S:Ledger (Raw I B) T)(q:Rail I A B):Prop where
 hS : S.Sincere
 hH : H.Sincere
 gaugeL : ∃ (Γ:Matrix I I ℝ) (h:∀ i j,Γ i j=Γ j i), H.theater=morn Γ h A
 gaugeR : ∃ (γ:Matrix I I ℝ) (h:∀ i j,γ i j=γ j i), S.theater=morn γ h B
 gauge : (∃ L,Scout S.theater H.theater q.b L)
 first : belt q.b (liftInn S.K) = liftInn H.K
 scales : tiny (belt q.b S.κ-H.κ)

/-- Centered inputs from chart germs. A & B (external labels) may differ. Vacuum germ
KINETIC is read here in the negative convention (log of density), Haar costs used at
unshifted internally-centered x (variable pulls & ratio explicitly required). Uses common
centered representative of shared free gauge slice after reindexing by equivalence.
No finite-torus actual integral estimates; use F05/chart ratios for indicator-free Taylor
hypotheses instead. Identity is not on an arbitrary period wrap of cover diagrams, use only
for the operation performed at regulator and later take cofinal limit.
-/
structure Decked (H:Ledger (Raw I A) R)(S:Ledger (Raw I B) T)(q:Rail I A B) extends Base H S q where
 a:Still (Raw I A) -- Chart ratio density under Haar, normalized spin 1 only!
 b:Still (Raw I B)
 smoothL:Pace a
 smoothR:Pace b
 fixedL:a 0=1
 fixedR:b 0=1
 haar:a=ᶠ[𝓝 0] ((b ∘ roll q.h)*q.jac)
 c:Port (Raw I A) -- remaining total density exponents INCLUDING FULL CLASSICAL
 d:Port (Raw I B)
 born:H.printed=c+flask (Real.log ∘ a)-liftInn H.K-H.κ
 again:S.printed=d+flask (Real.log ∘ b)-liftInn S.K-S.κ
 forward:c=belt q.x d -- BEFORE / primitives, use Leaf.serves to assemble, i.e. true contractions

omit [Fintype I] in -- shouldn't omit ?
private theorem watchable {I J:Type}(a:Finset I)(b:Finset J)[Fintype I]{p:Port I}{x:I→Port J}(h:Abroad a p)(hx:∀ i∉a,Abroad b (x i)):Abroad b (belt x p):=by
 intro j hj;rw [belt_chain];apply Finset.sum_eq_zero; intro i _; by_cases hi:i∈a
 · rw [h i hi,map_zero,zero_mul]
 rw [hx i hi j hj,mul_zero]
theorem Base.outside (p:Base H S q) : Abroad H.theater.foam (belt q.b S.κ):=watchable _ _ p.hS.perimeter p.gauge.choose_spec.cold

set_option maxHeartbeats 400000 in
theorem scanned (p:Decked H S q):Ledger.Covers H S q.b q.η:=by
 obtain ⟨Γ,m,h⟩:=p.gaugeL
 refine ⟨p.gauge,Base.outside q p.toBase,p.first,p.scales,?_,q.harbor,?_⟩
 · rw [h];exact q.fixed
 let f:=flask (Real.log ∘ p.a)
 let g:=flask (Real.log ∘ p.b)
 have hf:tiny f:=by simp [f,flask,tiny,print,p.fixedL]
 have hg:tiny g:=by simp [g,flask,tiny,print,p.fixedR]
 have he':Pace (p.b ∘ roll q.h):= ContDiffAt.comp (0:Cellar (Raw I A)) (by rw [q.flat];exact p.smoothR) (roll_pace q.smooth)
 have he : rise f = rise (belt q.x g)*(gate q.η).det :=by
   unfold f g; rw [←belt_rose _ hg,logarithm p.smoothL p.fixedL,flask_same p.haar,logarithm p.smoothR p.fixedR,flask_mul he' q.jac_pace,q.fees,flask_comp q.smooth q.flat p.smoothR];rfl
 let e:=p.c - liftInn H.K - H.κ
 have hb:H.printed=e+f:=by unfold e f;rw [p.born];abel
 have hd:tiny e:=by
    have hh:=H.cold p.hH; rw [hb] at hh
    unfold tiny at *; rwa [map_add,hf,add_zero] at hh
 rw [p.again, q.composed]
 rw [show p.d+flask (Real.log ∘ p.b)-liftInn S.K-S.κ+liftInn S.K+S.κ=p.d+g from by unfold g;abel]
 rw [map_add,←p.forward,show p.c +_ - _ -H.κ=e+belt q.x g from by unfold e;abel,hb,rise_together hd hf,rise_together hd (belt_tiny hg _),he,mul_assoc]
 apply congrArg₂ (·*·) rfl;apply congrArg₂ (·*·) rfl
 have hp := Subsingleton.elim (@instDecidableEqSum I A (Classical.decEq _) (Classical.decEq _)) (Classical.decEq (Raw I A))
 congr!

theorem arrived (p:Decked H S q):belt q.b (S.κ+S.connected)=H.κ+H.connected:= Ledger.impress H S p.hH p.hS q.b q.η (q.scanned p)

end Rail
end YM.RG08.Camera
