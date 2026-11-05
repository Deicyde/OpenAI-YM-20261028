import YM.MergeProof.Bootle
import YM.MergeProof.Garnet
import YM.MergeProof.Waver
import YM.Next.RANK.Anchor
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.TwoMasks
/-! Stake suppliers first axis always pinned cross coords. no bounds weakening. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Next.Rank Edition Baler Value Glyph Thirst Alarm Push GridApprox.Nil Motion Spindle Atlas Cells
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}(C:Family G)(N k p d m:ℕ) (v:Fin (m+1)→ C.label d)(b:ℝ) (Y:Points (m+1))(hk:k < N)
variable {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
local notation "L" => Listens C b (v:=m+1) hk.le p
local notation "Q"=> C.path.rep N p k
set_option quotPrecheck false
local notation "o'"=> seats C b Y hk.le p
lemma caught (H:C.Makes)(hp:C.ref d ≤ k)(τ:Course C N p k)(h: Geyser C W u ψ φ δ ζ r D)
    (he: Drake (Stock.census L) (Q).p.B o')(hK:Extra.Multi.Occupancy o' (r k)){x:ℝ}(hv:0<x)(hX:∀ i,x* Next.Rank.Spindle.paid C d k N p (v i) ≤ ζ d k): Stake m Y b hk.le v H hp τ x:=by
    let z:=o'; let f:= hops C N k p (m+1) b Y hk.le; let T:L→Motion:=plum C N k p _ b hk.le; let q:=τ.flow (Issued C b Y hk.le p v)
    have hy:q N le_rfl= _ := (τ.flow_self _).trans (wound C H N k p d (m+1) v b Y hk.le)
    have hh : Integrable (q N le_rfl) (prior G (C.side N p)):=by unfold q; rw [Course.flow_self]; exact (Array.stamped_cont _ _ (origin_int C b Y (k:=k) (N:=N) p v)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hf : f k=z:= funext fun i=> Tour.begin_anchor C p k _ -- edit
    have hs: Migrating C.path k p N f:=⟨fun i hi he=> funext fun j=> Work.I03.camp_step C p hi _⟩
    let w(_:L):= x
    let s (j:L):= v j.2
    have ht : (C.path.rep N p k).p=C.path.levels.budget k:=(H.wilson.represents N p k hk.le).vac
    have hx := h.at C d N k p W u ψ φ δ ζ r D s f T w H hp hk.le (hf.symm ▸ hK) hs (q:=q) (B:=Stock.census L)
    have hm:= hx (show Drake (Stock.census L) (C.path.levels.budget k).B (f k) by rw [hf,← ht]; exact he) (fun i=> hX _) (fun _=>hv) (fun i hi hp' => by unfold q; rw [τ.flow_step _ i hp', τ.same (i+1) (hi.trans i.le_succ) hp']) hy hh k le_rfl hk.le
    let A(j:L):= press hk.le b v j
    rw [marines k φ w (fun _=> hv), topPitch, if_neg hk.ne, ←ht,hf] at hm
    obtain ⟨U,V,hP,hT,hR,hq⟩:= hm
    let ht(j:L): (A j).Format 0 C.params Q:= satisfies hk.le b v j H hp
    have hi := (H.wilson.represents N p k hk.le).good
    obtain ⟨B,hB⟩:= somebody hi
    obtain ⟨ι,hI,I,hI',hL,hV⟩:= stokes z w U hP.exp hT (fun _=> hv)
    obtain ⟨κ,hg,K,hg',hL',hV'⟩:= knuckle z w V hP.flag hR (fun _=>hv)
    refine ⟨B,hB,ι,κ,hI,hg,I,K,hI',hg',hL,hL',fun u t _=>?_⟩
    have hT:= glint z (C.localSection d) A ht (hand C b hk.le p) (fp C b hk.le p) B (pinHat C d k) (pinReal C ..) U V K hV' hB I hV (fun i=> (hP.flag i).1)
    apply congr_arg (fun Y:Config G (C.side k p)→ veil L=> (Y u).part t) _; unfold fabricated;
    rw [← hT]; simp only [indexX,Ktone,hf] at hq; exact hq.symm -- tough f bind.B.Needs f(hf)
end YM.MergeProof.Accent
