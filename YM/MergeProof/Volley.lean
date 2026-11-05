import YM.MergeProof.Wallet
-- import Sails bulky? unavoidable separate later. no yet
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "WorkSite" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "Lℓ" => H.S.block i
variable (Q:GaugeDoor (H.rep N p (i+1)) (H.rep N p i))
-- AND unit private. C0 root cost for main axis; cQ≈Cred.Cover. calendar.
structure Volley (R:Rep G StartSite) (L:Side) (C w t:ℝ)(T:Heading F) (A:Wing→Prop) : Prop where
   -- insert Q binder
   main (j:F.Index): j≠0 → let v:=Size.axis F j; let Z:=Extra.Histories.primary (0:Site StartSite) v
    Coupon B H N p i Y (Z.exponentialEntry 0 B R) 0 0 Q A (Z.density 0 B R) (T.leads L v) (w*F.coeffSize (F.core v)) (C*F.coeffSize (Bid.vowel F L (F.core v))) t
   regular (f:g₀)(b:Support StartSite)(x:ℝ): let u:=(R).p.mass b x
    RegFit R 0 d Y b f→ (R).p.supBounds 0 b f x→ Coupon B H N p i Y (masked (R).p.threshold b f) 0 0 Q A (salary R b f) 0 (w*u) (w*u) (2*u)
   forced (f:g₀)(j:ℕ)(x:ℝ): let u:=(R).p.mass ((R).activities.forced j).support x
    f≠0 → A (.gasKey j)→ SlotFit R 0 j f→ 0≤x → (∀ U,‖f U‖≤x) → Coupon B H N p i Y 0 (exactGas (R).activities j f) 0 Q A (Extra.Histories.fare R j f) 0 (w*(u / Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (w*(u / Real.sqrt (H.levels.clock.forcedAllowance (i+1)))) (2*u)
   map_norm v : F.coeffSize (T.map v) ≤ C * F.coeffSize v ∧ F.coeffSize (T.map.symm v) ≤ C * F.coeffSize v
variable {H N p i Y B Q}{L:Side}{C w t:ℝ}{T:Heading F}{A:Wing→Prop}
lemma turnout {R}(he:Old=R)(h:H.S.block i=L)(hp:Volley B H N p i Y Q R L C w t T A): Stampede B H N p i Y Q C w t T A:=by
   subst L R; exact ⟨hp.main,hp.regular,hp.forced,hp.map_norm⟩
-- may `Heading` binder. and accidental notation
end YM.MergeProof
