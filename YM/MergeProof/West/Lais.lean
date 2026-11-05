import YM.MergeProof.Garnet
import YM.MergeProof.Waver
import YM.MergeProof.West.Dart
import YM.MergeProof.West.Pamu
import YM.MergeProof.West.Sylva
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.TwoMasks



set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Next.Rank Edition Baler Value Glyph Thirst Alarm Push GridApprox.Nil Motion Spindle Atlas Cells
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V]
variable (C:Family G)(h:C.Makes)(N k p m:ℕ){d:Fin m→ℕ}(v:(i:Fin m)→ C.label (d i)) (b:ℝ)(Y:Points m)(hk:k≤N)
local notation "T"=> Ship.yard C b hk p
local notation "Q"=> C.path.rep N p N
set_option quotPrecheck false
local notation "L"=> Listens C b (v:=m) hk p
local notation "v'"=> hops C N k p m b Y hk
local notation "g'"=> plum C N k p m b hk
local notation "P"=> IssuedX C b Y hk p v
include h
lemma woundX : IssuedX C b Y hk p v=birth (Stock.census (Listens C b (v:=m) hk p)) Q (fun i=> item C (d i.2) N p (v i.2) (fun j=> hops C N k p m b Y hk j i) (plum C N k p m b hk i)):=by
    let J:= originX C b Y k N p v
    have hv := logged Q T J (C.beta N p) (h.wilson.starts N p|>.2)
    have hV:P= birth (Stock.census _) Q (fun i=>(T).copy i.1 (J i.2)):= hv
    rw [hV]; congr 1; funext i U
    have hx:= congr_fun (stamp_singleX C b Y hk p v i) U
    change (IssuedX _ _ _ _ _ _ _).part _ = _ at hx; rw [hV,boot,(h.wilson.starts N p).2] at hx
    let z:= v' N i; have he:z=(C.S.toDepth hk p).embed (seats C b Y hk p i):= by unfold z hops Mix.camp; rw [dif_pos hk]
    unfold item; change _= scalar (g' i) ((C.O N p (v i.2) 0) (pull (g' i).1 z U)); rw [he]; simp only [plum,calling]; unfold singleP at hx; dsimp only [Function.comp_apply] at hx; rw [bare_pull,dot_move] at hx
    exact mul_left_cancel₀ (show (bare (C.beta N p) U:ℂ)≠0 from Complex.ofReal_ne_zero.mpr (bare_pos ..|>.ne')) hx
end YM.MergeProof.Accent

namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Next.Rank Edition Baler Value Glyph Thirst Alarm Push GridApprox.Nil Motion Spindle Atlas Cells
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}(C:Family G)(N k p m:ℕ){d:Fin (m+1)→ℕ}(v:(i:Fin (m+1))→ C.label (d i))(b:ℝ) (Y:Points (m+1))(hk:k < N)
variable {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
local notation "L" => Listens C b (v:=m+1) hk.le p
local notation "Q"=> C.path.rep N p k
set_option quotPrecheck false
local notation "o'"=> seats C b Y hk.le p
lemma caughtX (H:C.Makes)(hp:∀ i, C.ref (d i) ≤ k)(τ:Course C N p k)(h: Geyser C W u ψ φ δ ζ r D)
    (he: Drake (Stock.census L) (Q).p.B o')(hK:Extra.Multi.Occupancy o' (r k)){x:ℝ}(hv:0<x)(hX:∀ i,x* Next.Rank.Spindle.paid C (d i) k N p (v i) ≤ ζ (d i) k): StakeX m Y b hk.le v H hp τ x:=by
    let z:=o'; let f:= hops C N k p (m+1) b Y hk.le; let T:L→Motion:=plum C N k p _ b hk.le; let q:=τ.flow (IssuedX C b Y hk.le p v)
    have hy:q N le_rfl= _ := (τ.flow_self _).trans (woundX C H N k p (m+1) v b Y hk.le)
    have hh : Integrable (q N le_rfl) (prior G (C.side N p)):=by unfold q; rw [Course.flow_self]; exact (Array.stamped_cont _ _ (origin_intX C b Y (k:=k) (N:=N) p v)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hf : f k=z:= funext fun i=> Tour.begin_anchor C p k _ -- edit
    have hs: Migrating C.path k p N f:=⟨fun i hi he=> funext fun j=> Work.I03.camp_step C p hi _⟩
    let w(_:L):= x
    let s (j:L):= v j.2
    have ht : (C.path.rep N p k).p=C.path.levels.budget k:=(H.wilson.represents N p k hk.le).vac
    have hx := h.sylvan C (fun i:L=>d i.2) N k p W u ψ φ δ ζ r D s f T w H (fun i=> hp _) hk.le (hf.symm ▸ hK) hs (q:=q) (B:=Stock.census L)
    have hm:= hx (show Drake (Stock.census L) (C.path.levels.budget k).B (f k) by rw [hf,← ht]; exact he) (fun i=> hX _) (fun _=>hv) (fun i hi hp' => by unfold q; rw [τ.flow_step _ i hp', τ.same (i+1) (hi.trans i.le_succ) hp']) hy hh k le_rfl hk.le
    let A(j:L):= pressX hk.le b v j
    rw [marines k φ w (fun _=> hv), topPitch, if_neg hk.ne, ←ht,hf] at hm
    obtain ⟨U,V,hP,hT,hR,hq⟩:= hm
    let ht(j:L): (A j).Format 0 C.params Q:= satisfiesX hk.le b v j H hp
    have hi := (H.wilson.represents N p k hk.le).good
    obtain ⟨B,hB⟩:= somebody hi
    obtain ⟨ι,hI,I,hI',hL,hV⟩:= stokes z w U hP.exp hT (fun _=> hv)
    obtain ⟨κ,hg,K,hg',hL',hV'⟩:= knuckle z w V hP.flag hR (fun _=>hv)
    refine ⟨B,hB,ι,κ,hI,hg,I,K,hI',hg',hL,hL',?_⟩
    have hT:= glintX z (fun i:L=> C.localSection (d i.2)) A ht (hand C b hk.le p) (fp C b hk.le p) B (fun i=>pinHat C (d i.2) k) (fun i=>pinReal C ..) U V K hV' hB I hV (fun i=> (hP.flag i).1)
    unfold fabricatedX; rw [← hT]; simp only [indexX,Ktone,hf] at hq; exact hq.symm
end YM.MergeProof.Accent