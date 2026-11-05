import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Installation
import YM.MergeProof.South.Bus
import YM.MergeProof.South.Window
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
local notation "ζ!"=> ζ d
section
variable {I B:Type}[Fintype I][Fintype B](a:I→ℂ){x:I→ℝ}(hw:0<w)(hx:∀ i,0 < x i)(hz:∑ i,w*‖a i‖/x i≤1)
include hw hx hz
-- charge summed absolutely; same bill as Wakes portfolio. 
lemma fare (F':I→B→ℂ) {p:ℝ}(hp:0≤p)(h:∀ i,x i*(∑ j,‖F' i j‖)≤p) : w*(∑ j,‖∑ i,a i*F' i j‖)≤p:=by
    let c i:= w*‖a i‖/x i; let t(i:I):= x i*∑ j,‖F' i j‖
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=> norm_sum_le ..)) hw.le) ?_
    simp_rw [norm_mul]; rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]; rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (fun i _=> show w*(‖a i‖*∑ j,‖F' i j‖) ≤ c i*p from ?_)) ?_
    · have ht:0 < x i:=hx i
      exact le_trans (le_of_eq (b:=c i*t i) (by unfold c t; field_simp)) (mul_le_mul_of_nonneg_left (h i) (show 0 ≤ c i from by unfold c; positivity))
    rw [← Finset.sum_mul]; exact mul_le_of_le_one_left hp hz
lemma fare1 (F':I→ℂ){p:ℝ}(hp:0≤p)(h:∀ i,x i*‖F' i‖≤p) : w*‖∑ i,a i*F' i‖≤p:=by simpa using fare w a hw hx hz (fun i (_:Unit)=>F' i) hp (fun i=> by simpa using h i)
end
section
variable {I V:Type}[Fintype I][Fintype V][DecidableEq V] {B:Census V}(h:Scrim C W u ψ φ δ ζ r D)
variable (o:∀ i:ℕ,V→Site (C.side i p)){x:I→ℝ}(s:V→Motion)(a:V→I→ℂ) (Z:I→∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)) {g:I→ℕ→ℝ}
   (e:k≤N)(hw:0<w)(hx:∀ i,0 < x i)(hz:∀ i,∑ j,w*‖a i j‖/x j≤1)
local notation "t!"=> march (fun _ : V=>w) φ m
local notation "f"=> fun i j=>∑ n, a j n • liftF T Y! N p (s j) (fun l=>o l j) (Z n) i
local notation "p!"=> fun i j=>∑ n, a j n • liftK T N p (s j) (fun l=>o l j) (Z n) i
include H h
set_option maxHeartbeats 800000 in
lemma prolonged {M:Config G (C.side k p)→Poly B} (ht:ℓ ≤ m)(hk:m≤k)(hi: Integrable M (prior G _))(hη:Migrating T m p k o)(hM:Occupancy (o m) (r m)) (hm:Drake B (T|>.levels.budget m).B (o m)) (he:∀ i:I,Club T C.params Y! (ζ d) ψ m k N p (stair φ (x i) m) D (Z i) (g i) e) (hQ:Served (R k) (f k) (p! k) M (o k) (t! k) (C.path.levels.budget k).supportExponent 1) (hw:0<w)(hx:∀ i,0<x i)(hz:∀ i,∑ j,w*‖a i j‖/x j≤1): Served (R m) (f m) (p! m) (gust T N p k M m hk) (o m) (fun i=>w) (C.path.levels.budget m).supportExponent 1∧ Vault (fun _=>w) (f m) (p! m) 2 1:=by
    let X i j:= liftF T Y! N p (s i) (fun l=>o l i) (Z j); let Y i j:=liftK T N p (s i) (fun l=>o l i) (Z j)
    let q:= gust T N p k M; let f':= f; let p':= p!; let W':= t!
    choose G' H' hp' hP using fun (i:V)(j:I)=>beams C N k m p d H (x j) h (s i) (o:=fun l=>o l i) (Z j) ht hk e (hx j) (fun l hl hL=> (congr_fun (hη.mare l hl hL) i).symm) (he j)
    let K j (i:V):= ∑ l, a i l • G' i l j
    have hh (i:V) : (fun j=> W' j i)=stair φ w m:=by
       funext j; induction j with
       | zero=> rfl
       | succ j hj=> by_cases hp : m ≤ j
                     · unfold W' stair;simp only [march,if_pos hp]; exact congr_arg (φ j * ·) hj
                     unfold W' stair;simp only [march,if_neg hp]
    have hW (i:V) : Wakes T m k N p (fun j=>o j i) (fun j=>W' j i) (fun j=>f' j i) (fun j=>K j i) D e:=by rw [hh i]; exact rearranged C N k m p H w h (a i) e hw hx (hz i) (H' i) (fun j l hl hL=> (hp' i j l hl hL).2)
    have hj(j)(hr:m ≤ j)(hn:j ≤ k): tapes T p N K j=p' j:=by
       unfold p'; funext i; change profile _ (K j i)=_
       have hx(l): Dominated (a i l • G' i l j):= rainbow ((H' i l).stocked j hr hn) _
       simp_rw [K, prof_sum _ hx, profile_scale]; exact Finset.sum_congr rfl fun n _=> congr_arg _ ((hp' i n j hr hn).1)
    have hF:Brine C.path m δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=> h.costs.stay.support _ (Nat.zero_le i)⟩
    have H':=Accent.window T r δ u D N p e o W' f' K H.wilson (desal C.path r m p k δ φ o (fun _=>w) (fun _=>hw) hF B hη hm h.costs.mom hM) h.costs.night hW (show Served _ (f' k) (tapes T p N K k) M _ (W' k) _ _ from (hj k hk le_rfl).symm ▸ hQ) hi m le_rfl hk
    rw [hj m le_rfl hk, show W' m=(fun _=>w) from marines m φ _ (fun _=>hw)] at H'
    refine ⟨H',⟨fun i U=>?_,fun i U=>?_⟩⟩
    · refine le_trans ?_ (fare1 w _ hw hx (hz i) (fun j=> X i j m U) zero_le_two (fun j=> hP i j U|>.1)); simp_rw [Finset.sum_apply]; rfl
    rw [← Finset.mul_sum]
    simp_rw [Finset.sum_apply]; exact fare w _ hw hx (hz i) (fun j l=>Y i j m l U) zero_le_one (fun j=>by
       have h:= (hP i j U).2; rw [(hp' i j m le_rfl hk).1] at h; exact h)
end
end YM.MergeProof
