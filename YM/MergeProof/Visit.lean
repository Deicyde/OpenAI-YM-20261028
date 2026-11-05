import YM.MergeProof.Wallet
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
section
-- re-use score explicitly.
variable {R:Rep G (H.S.side i p)}{E:Rep G (H.S.side (i+1) p)}
variable (he : H.rep N p i=R) (h : H.rep N p (i+1)=E)
   (Q:GaugeDoor E R)
-- move door definition for any m, oriented actions. Maintain casts. on any layout.
def duet : GaugeDoor Old Rout:= he.symm ▸ h.symm ▸ Q
lemma peels (A:Wing→Prop)(α:g₀)(ρ:Res G StartSite)(β:ℕ → Config G WorkSite→ℂ)(δ:ℂ)(u:ℂ)(a t:ℝ)(X : Site StartSite)(b : Site WorkSite)(hp: Tale A X b u α ρ (profile R.activities β) δ a t Q): Tale A X b u α ρ (profile (Rout).activities β) δ a t (duet H N p i he h Q):=by
   subst E R; exact hp
lemma sound_duet (S:StepData WorkSite StartSite) (hp:SoundDoor S Q): SoundDoor S (duet H N p i he h Q):=by subst E R; exact hp
lemma border (A:Wing→Prop)(α:g₀)(ρ:Res G StartSite)(f:g₀) (a t u:ℝ)(lead:F.Coeff)(L:Side)(hw:H.S.block i=L)(P:Coefficient F WorkSite)(hq:Gig B H N p i Y f P lead a t)
    (hp:Tale A 0 0 ((L.val:ℂ)^d) α ρ (profile R.activities P.forced) 0 u t Q): Coupon B H N p i Y α ρ 0 (duet _ _ _ _ he h Q) A f lead a t u:=by
   subst L; exact ⟨P,hq,peels H N p i he h Q A α ρ _ _ _ _ _ _ _ hp⟩
end
end YM.MergeProof
