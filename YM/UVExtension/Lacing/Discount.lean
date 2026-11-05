import YM.UVExtension.Lacing.Arbor
import YM.UVExtension.Lacing.Rooms
/-!
 # Graph-step architecture. at every complex coordinate its inputs under Motion may be OTHER values of the parameter.
 Hence require *family* per motion. cone delivered, eq genuine. Strong stability even without complex orientation equations.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Motion Next.Foundations
open Bid Concert BoundedContinuousFunction Eyelet RoutesF Work.G08
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n n':Side}{d:ℕ} {F:Frame G d}{p P :BudgetPoint}{H:Hol G}
local notation "R"=> RoutesF F n n' p P H
local notation "E"=> Cow G n' p d H
local notation "B"=> Cow G n P d H
local notation "Lc"=> Bucket F P H n
set_option quotPrecheck false
variable (L:Motion→RoutesF F n n' p P H)(Y Y':Motion→(F.Coeff→ₗ[ℂ] Cow G n' p d H))(hn:2≤ n.val)
local notation "a'"=> major L Y hn
local notation "b'"=> minor L Y hn
local notation "F1"=> F.Coeff
variable {L Y hn}
variable {u v c w s:ℝ} {r:Side}{T:Heading F} (h:Tollgate F u v c w s)
variable (hR: ∀ i:Motion, (Tips (L i) r T u v)) (hp:∀ x:F.Coeff,F.coeffSize (T.map x) ≤ c*F.coeffSize x ∧ F.coeffSize (T.map.symm x) ≤ c* F.coeffSize x)(hh: ∀ i x, ‖Y i x‖ ≤ s*F.coeffSize (F.core x))
include h hR hp hh
set_option synthInstance.maxHeartbeats 120000
lemma discount (hn: 2 ≤ n.val){B':ℝ}(hb:0 ≤ B') (hx:∀ i x, ‖Y' i x‖ ≤ s*F.coeffSize (F.core x)) (hz:∀ i x, ‖Y i x-Y' i x‖≤ B'*s*F.coeffSize (F.core x))(x:F.Coeff): ‖crown L Y hn x-crown L Y' hn x‖ ≤ B'*(1/8)*w*F.coeffSize (F.core x):=by
    let M:= major L Y hn; let N:=major L Y' hn; let S:=minor L Y hn; let Q:= minor L Y' hn; let A:=steer L Y hn
    let k x:=F.coeffSize (F.core x); have hw:=h.t_now; have hs:=h.t_next; have hv:= (hR (1,true)).counts.calm; have hA:=orbitCost_one_le F
    let d:= crown L Y hn; let e:= crown L Y' hn; obtain ⟨i,hi⟩:=(carat h hR hp hh hn).2 x; subst x
    -- retain expression atlas
    let g:= M i-N i; let p:=2*u*(B'*s)*orbitCost F
    have hf:d (M i)= S i:= pilfer h hR hp hh hn i; have hq:e (N i)=Q i:= pilfer h hR hp hx hn i; rw [pilfer h hR hp hh]
    have he : S i-e (M i)=(S i-Q i)-e g:=by rw [show e g=e (M i)-e (N i) from map_sub ..,hq]; abel
    obtain ⟨h1,h2⟩:=beams L Y Y' hn hR (by positivity) hz i; unfold S e M at he; rw [he]; apply (norm_sub_le ..).trans
    have hx' := le_trans (brunt h hR hp hx hn g) (mul_le_mul_of_nonneg_left (le_trans (size_core F g) h1) (by linarith));
    calc
       _ ≤ p*k i+w*(p*k i):= by convert! add_le_add h2 hx'
       _ ≤ _ := by
          change p*k i+w*(p*k i) ≤_
          calc
             _=(1+w)*p*k i:=by ring
             _≤(1+w)*p*(2*c*k (M i)):=mul_le_mul_of_nonneg_left (Gate h hR hp hh hn i|>.2.1) (by unfold p; positivity)
             _=(B'*((1+w)*(2*u*s)*orbitCost F*(2*c)))*k (M i):=by unfold p; ring
             _ ≤ _:= mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left h.orbit hb).trans_eq (mul_assoc ..).symm) (size_nonneg ..)
end YM.UVExtension.Lacing
