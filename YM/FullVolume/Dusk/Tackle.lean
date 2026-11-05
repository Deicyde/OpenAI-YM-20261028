import YM.MergeProof.Balloon
import YM.FullVolume.Dusk.Placed
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Exponential
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(v:C.label d)(a:ℝ)(ha:0<a)(B:Stock.Tabs C.path.levels)
variable (H:C.Makes) {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Ponds C W u ψ φ δ (fly C.path.levels) r D p k N) (hx:∀ i:ℕ, 1≤r i)
set_option quotPrecheck false
local notation "b!"=> Cells.center C.S p
local notation "T"=> C.path.levels
local notation "A"=> Site (C.side m p)
local notation "P"=> C.path.levels.budget
local notation "F"=> C.labels.level d
-- centered at site zero only. Root N large after m. Works when opens L.T.
include B h H hx ha
lemma tentF (hm: Stock.Tabs.opens C.path.levels 1 m k)(hd:C.ref d ≤ m) (hN:k<N)(he:(F).coeffSize v≤a):
    (Cells.center C.S p (hm.1.trans hN.le) 0).rootTest (C.beta N p) (C.O N p v 0) ≤ Real.exp (expense C a m k d):=by
   let hn:m ≤ N:= hm.1.trans hN.le; let X:= b! hn 0
   let w:= plumR C d a k; let f(j):=(Mix.camp C p m j); let nu(i:A):=dye (X.omega i) (X.hand i); let t(i:A):= item C d N p v (fun j=> f j i) (nu i)
   let K:= Fintype.card A; let Y:= Stock.census A
   have hp:Migrating C.path k p N f:= ⟨fun j hi _=> funext fun i=> Work.I03.camp_step C p (hm.1.trans hi) i⟩
   have hv := Work.I03.answer G C 1 le_rfl B m k hm N hN.le p hn
   have hs(i:A): X.copy i (C.O N p v 0)=t i:=by
      funext U; have hh : f N i= X.copyMap i 0:= (hv.1 i).symm
      unfold t item stepUp;change _=scalar (nu i) (C.O N p v 0 (pull _ (f N i) _)); simp_rw [nu,calling]; rw [hh,show X.copyMap i 0=X.translateBy i from ?_]; rfl
      change (X.omega i).act 0+_= _; simp
   have hf: Edition.Spaced (P k|>.B) (f k):= fun i j hij=>by
       have he':= hv.2.2 k le_rfl hN.le i j hij; rw [mul_one] at he'; exact_mod_cast he'
   have hk:0<w:= stockpit C k d a ha
   let z(i:A):=w
   have hR:m≤k:=hm.1
   have hj:= occursT (B:=Y) C N k p d H h f (fun _=>v) nu (w:=z) hN (hd.trans hR) (fun _=>hk) (fun _=>stocking C N k p d v a ha (hd.trans hR) hN.le H he) hp (fun i=> (Extra.Multi.Occupancy.of_injective (Edition.injected _ _ (P k|>.B_pos) hf) i).trans (hx _)) ⟨fun _ _ i _ j _=> hf i j⟩ (Stock.final A)
   have hz : Poly.toll (R:=Stock.census A) z (Stock.final A)=w^K:=by simp [Poly.toll, K, z,Stock.final]
   have hw := C.S.a_pos k
   unfold Tiling.rootTest; change ‖moment (C.beta N p) (fun U=>∏ i:A,X.copy i _ U)‖^_ ≤ _; simp_rw [hs]
   let W:= C.omega N p (fun U=>∏ i:A,t i U); let g:=(C.S.a m/C.S.a k)^4*Vac.treasury T k+ (6:ℝ)
   rw [hz] at hj
   refine (Stock.spacer ‖W‖ g w K (norm_nonneg _) hk Fintype.card_pos ?_).trans (by change Real.exp g/w ≤ Real.exp (g-_); rw [Real.exp_sub,Real.exp_log hk])
   have he : (Fintype.card (Site (C.side k p)):ℝ)*Vac.treasury C.path.levels k+K* (6:ℝ)=K*g:=by
       rw [Stock.tallies C.S m k p]; unfold K g; ring
   exact hj.trans_eq (congr_arg Real.exp he)
end YM.MergeProof.Accent
#print axioms YM.MergeProof.Accent.tentF
