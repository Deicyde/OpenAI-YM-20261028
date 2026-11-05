import YM.MergeProof.Caprese
import YM.MergeProof.Coast

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Exponential
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(v:C.label d)(a:ℝ)(ha:0<a)(B:Stock.Tabs C.path.levels)
variable (H:C.Makes) {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (hx:∀ i:ℕ, 1≤r i)
set_option quotPrecheck false
local notation "b!"=> Cells.center C.S p
local notation "T"=> C.path.levels
local notation "A"=> Site (C.side m p)
local notation "P"=> C.path.levels.budget
local notation "F"=> C.labels.level d
variable (b: Config G (C.side N p)→ℂ) (Z:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)) (z ζ:ℕ→ℝ)
def stakes (m k:ℕ):=Real.exp ((C.S.a m/C.S.a k)^ (4:ℕ)*Vac.treasury C.path.levels k+5)
include B H hx
lemma filling (w:ℝ) (x:Motion) (hm: Stock.Tabs.opens C.path.levels 1 m k)(hd:C.ref d ≤ k)(hN:k<N)(hk:0<w) (he:Yeast C.path C.params (C.localSection d) ζ u ψ k N p (fun i=> march (fun _:Unit=>w) φ k i ()) b D Z z)
    (hf':Fiesta C.path (C.labels.level d) ζ ψ k)(hu: Moonlit C.path r δ u D)(hi:∀ i,k ≤ i→ φ i ≤1)(hr:Brine C.path k δ φ)(hR:Monotone r)(hc:Continuous b) : (Cells.center C.S p (hm.1.trans hN.le) 0).rootTest (C.beta N p) (dance x b) ≤ stakes C m k/w:=by
   let hn:m ≤ N:= hm.1.trans hN.le; let X:= b! hn 0
   let f(j):=(Mix.camp C p m j); let nu(i:A):=dye (X.omega i) (X.hand i); let θ i:= twist (nu i) x; let t(i:A):=stepUp (θ i) (f N i) b
   let K:= Fintype.card A; let Y:= Stock.census A
   have hp:Migrating C.path k p N f:= ⟨fun j hi _=> funext fun i=> Work.I03.camp_step C p (hm.1.trans hi) i⟩
   have hv := Work.I03.answer G C 1 le_rfl B m k hm N hN.le p hn
   have hs(i:A): X.copy i (dance x b) = t i:=by
      funext U; have hh : f N i= X.copyMap i 0:= (hv.1 i).symm
      rw [show t i U= scalar (twist (nu i) x) (b (pull _ (f N i) U)) from rfl,← oper,hh, show X.copyMap i 0=X.translateBy i by change (X.omega i).act 0+_= _; simp]; simp_rw [nu,calling]; change dot (X.hand i) (scalar x (b (pull x.1 0 (pull (X.omega i) (X.translateBy i) U)))) = dot (X.hand i) (scalar x (b (pull (X.omega i*x.1) (X.translateBy i) U))); rw [pull_pull]; simp [affine]
   have hf: Edition.Spaced (P k|>.B) (f k):= fun i j hij=>by
       have he':= hv.2.2 k le_rfl hN.le i j hij; rw [mul_one] at he'; exact_mod_cast he' -- coe maybe cast
   let z(i:A):=w
   have hj:= baking (B:=Y) C N k p d H f θ b Z _ w ζ hN hd hk he hf' hu hi hr hR hc hp (fun i=> (Extra.Multi.Occupancy.of_injective (Edition.injected _ _ (P k|>.B_pos) hf) i).trans (hx _)) ⟨fun _ _ i _ j _=> hf i j⟩ (Stock.final A)
   have hz : Poly.toll (R:=Stock.census A) (fun _:A=>w) (Stock.final A)=w^K:=by simp [Poly.toll, K,Stock.final]
   unfold Tiling.rootTest; change ‖moment (C.beta N p) (fun U=>∏ i:A,X.copy i _ U)‖^_ ≤ _; simp_rw [hs]
   let W:= C.omega N p (fun U=>∏ i:A,t i U); let g:=(C.S.a m/C.S.a k)^4*Vac.treasury T k+ (5:ℝ)
   rw [hz] at hj
   refine Stock.spacer ‖W‖ g w K (norm_nonneg _) hk Fintype.card_pos ?_
   have he : (Fintype.card (Site (C.side k p)):ℝ)*Vac.treasury C.path.levels k+K* (5:ℝ)=K*g:=by
       rw [Stock.tallies C.S m k p]; unfold K g; ring
   exact hj.trans_eq (congr_arg Real.exp he)
end YM.MergeProof.Accent
