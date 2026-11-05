import YM.MergeProof.Bungalow
import YM.MergeProof.South.Window
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Turbine
import YM.Push.GRID_APPROXIMATION.Birth

/-! lease connector.Full census used from same offset, minus coe retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu Overlay Cells
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V : Type} [Fintype V][DecidableEq V]{B:Census V}{G:Gauge}
open GridApprox Local Extra.Trajectories Source Extra.Multi GridApprox.Joint
section
set_option linter.unusedSectionVars false
variable (A:History G)(N p:ℕ){k j:ℕ}(Y:Config G (A.S.side j p)→Poly B)
lemma gust_choose (h:Integrable Y (prior G _))(hk:k≤j)(s:B.Mode) : (fun U=> (gust A N p j Y k hk U).part s)=pushTo A N p hk (fun U=> (Y U).part s):=by
   induction hk using Nat.decreasingInduction with
   | self=> rw [gust_base,pushTo_self]
   | of_succ i hi IH=>
      rw [gust_step A N p j Y hi, Birth.push_first A N p hi]
      exact (push_get (A.levels.transition_mass ..) (gust_live A N p _ _ h hi) s).trans (by rw [IH])
end
section
variable (A:History G)(N p:ℕ){m k:ℕ}(h:m≤k)(hk:k≤N) (D: Config G (A.S.side N p)→ℂ)(Q:Config G (A.S.side k p)→ℂ)
set_option quotPrecheck false
local notation "b!" => Stock.census (Site (A.S.side m p))
local notation "T"=>tilesAt A.S p h
local notation "Y"=>tilesAt A.S p (h.trans hk)
local notation "L"=> birth (b!) (A.rep N p N) (fun i=>- ((Y).copy i D))
local notation "M"=> gust A N p N (L) k hk
local notation "X"=> couple M (fun i=> (T).copy i Q)
lemma joins (hp : A.Selected) (hX:Integrable L (prior G _)) (s:(b!).Mode) : (fun U=> (X U).part s)=GridApprox.Joint.join A N p h hk D Q s.val :=by
   funext U; let W:= (T); let v i:=W.copy i Q U
   have he (t:(b!).Mode): (M U).part t=pushTo A N p hk (fine A N p D (h.trans hk) t.val) U:=by
      have hp' : (fun U=>(L U).part t) = fine A N p D (h.trans hk) t.val:=by funext U; unfold birth fine; simp only [Poly.part_smul,Mach, pass_fire,(hp.starts ..).2]; rfl
      have h:= gust_choose A N p L hX hk t; rw [hp'] at h; exact congr_fun h U
   have hz : Poly.pass (Mach (b!) v)=∏ i,(1+Poly.send ((b!).fire i) (v i)):=by
      unfold Mach; rw [pass_sum]; intro i _; exact singleton_nonempty _
   change ((M U)*Poly.pass (Mach (b!) v)).part s= _
   rw [hz]
   let t:=s.val; let L':=(M U)
   have hp := GridApprox.Birth.array_read L' t v
   refine hp.trans (Finset.sum_congr rfl (fun i _=> ?_)); apply congr_arg₂ (·*·); exact he _; rfl
lemma comes (hp : A.Selected) (hX:Integrable L (prior G _)) (hD:Envelope D)(hV:Envelope Q) : Integrable X (prior G _):=by
   have hh (s:(b!).Mode) : Integrable (fun U=>(X U).part s) (prior G _):=by rw [joins A N p h hk D Q hp hX]; exact GridApprox.Joint.joined A N p h hk hD hV _
   exact (MeasureTheory.integrable_pi_iff).mpr hh
set_option maxHeartbeats 800000 in
lemma conducts (hp : A.Selected) (hX:Integrable L (prior G _)) (hD:Envelope D){n:ℕ} (hV:Interior (GridApprox.window 0 n) Q)(hW : GridApprox.room A.levels m k n) (s : (b!).Mode) (i:ℕ) (hi:i ≤ k): (∫ U,(gust A N p k X i hi U).part s∂prior G _)=(Wilson.partition G (A.S.side N p) (A.β N p N):ℂ)*moment (A.β N p N) (cutoff A N p h hk D Q s.val):=by
   let f U:= (X U).part s; let l:= (gust A N p k X i hi); let c := X
   have hx:= comes A N p h hk D Q hp hX hD (cylinder_env hV)
   have hl : Integrable f (prior G _):= ((Poly.get s).restrictScalars ℝ).integrable_comp hx
   have hh:= gust_choose A N p X hx hi s
   exact Eq.trans (congr_arg (fun f:Config G (A.S.side i p)→ℂ => ∫ U,f U∂prior G _) hh) (Eq.trans (pushTo_integral A N p hi f hl) (Eq.trans (congr_arg (fun f:Config G (A.S.side k p)→ℂ => ∫ U,f U∂prior G _) (joins A N p h hk D Q hp hX s)) (Joint.restored A N p h hk hD n hV hW s.val)))
end
end YM.MergeProof.Accent
