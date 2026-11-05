import YM.Extra.SOURCE_HISTORIES.PaddedBolt
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Withdrawal
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Primer
/-! # Channel correspondence -- coordinate vectors and choices spun in actual orientation.
 Requires NO independent calibration. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f C F: Side} {P : Patch} {M : ℕ}
section rise
variable (h : C.val=c.val*M) (s:Signed)
local notation "w" => Macrame.normal (divides h) h
local notation "p" => (splitter (divides h))
include h
lemma orbitEdges (i:Bond C): curr p (Channel.edge s i)=Channel.edge s (curr p i):= by
  rcases i with ⟨i,d⟩; change _= Channel.edge s (p i,d)
  cases h': s.flip d
  · rw [positive s _ h', positive s _ h']; exact Prod.ext (usual (divides h) s i).symm rfl
  rw [negative s _ h',negative s _ h']; refine Prod.ext ?_ rfl
  change p (s.act (i+step d))= s.act (p i+step d); rw [← usual]; exact congr_arg _ ((w).step_up ..)
lemma constellation (V:Config G c) : pull s 0 ((w).links V)= (w).links (pull s 0 V) := by
  funext i; rw [Channel.charge]; change _=pull s 0 V (curr p i); rw [Channel.charge]; change (if _ then (V (curr p (Channel.edge s i)))⁻¹ else V (curr p (Channel.edge s i)))=_; rw [orbitEdges h]; rfl
lemma orbitData (V:Config G c) (u : Directions G c): displacement s (u ∘ curr p) ((w).links V)=(displacement s u V ∘ curr p):= by
  funext i; change (if s.flip i.2 then -(G.adjoint (V (curr p (Channel.edge s i)))⁻¹ (u (curr p (Channel.edge s i)))) else u (curr p (Channel.edge s i)))= _; rw [orbitEdges h]; rfl
lemma starsL (x y : Site C) (hp : 2*separation x y < c.val): lift (y-x)= lift (p y - p x):= by
  symm; apply lift_eq_iff.mpr; refine ⟨?_,fun i=>?_⟩
  · rw [← map_sub]; exact Eq.trans (congr_arg p (wrap_lift (y-x)).symm) (branch ..)
  rw [separation_comm] at hp; unfold separation at hp; have hx := Lattice.component_le (y-x) i; omega
end rise
section bubble
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} (hC : C.val=c.val*M) (he:2 ≤ c.val)
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
abbrev fineP (h : f.val=c.val*P.L.val) (H:F.val=C.val*P.L.val) (hC:C.val=c.val*M): F.val=f.val*M:=by rw [H,h,hC]; ac_rfl
-- input tag not replicate as actual field permutations; need only prediction.
include hC he

lemma spun (V:Config G f) (t:(S).Choices) (s:Signed) (hp:P.Branches Q G) : (Y).prediction (pull s 0 ((L).high.links V)) (choice s ((L).pullTag Q t))=(L).low.links ((S).prediction (pull s 0 V) (choice s t)):= by
  rw [(Oriented.carry s (show (Y).patch.Branches (Y).kernel G from hp) ..).2,Lace.predicts,(Oriented.carry s (show (S).patch.Branches (S).kernel G from hp) ..).2]; exact constellation hC s ((S).prediction V t)
end bubble
end YM.PhysicalNext.Repeat.Deck
