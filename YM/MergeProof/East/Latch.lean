import YM.MergeProof.East.Pint
import YM.MergeProof.East.Shine
import YM.UVNext.UV_STATION_TRANSFER.Single

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ} {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ι → Tapes.Panel D) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ φ δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "S"=> standard C
variable (z:ℝ) (hZ : ∀ i≤D,Accent.generator G i≤ z)
open Analysis Next.UVStress Climb Ward
include H h hZ hp
open Glimmer
lemma second (F:Extraction.Order)(hn:2 ≤ n)(x:ι)(b:ℝ)(hb:(P x).arc ≤ b)(d:Fin (D+1))(v:C.label d) :∃ Q:ℝ,0 ≤ Q ∧ ∀ᶠ k:ℕ in atTop, ∀ Y,Poised P B H O J n z k Y→
     ∀ᶠ i in F.fuse, centeredBudget C ⟨d,ladd C (mag A b k) k i.1 i.2 d (Y i.1 i.2 d) v⟩ (Q*Perch.bill ((b-(P x).arc)*D) (clim A k)) (Next.Rank.Station.width A (P x).arc k) i.1 i.2:=by
    let S':= C.labels.level d;let I:=S'.Index;let a:=(P x).arc;let e:=b-a; have hE:0≤e:= sub_nonneg.mpr hb
    let χ (i:I):C.label d:= Pi.single i 1
    choose Q hQ ht using fun i:I=> sole P B H h hp O J z hZ F hn x d (χ i)
    let X(i):= ‖v i‖ * Q i; let w:= ∑ i,X i; have hw: 0≤w:=Finset.sum_nonneg fun i _=>mul_nonneg (norm_nonneg (v i)) (hQ i)
    refine ⟨w,hw,?_⟩; filter_upwards [eventually_all.mpr ht] with k hx Y hY
    filter_upwards [large_mesh F (k+1),eventually_all.mpr (fun i:I=>hx i Y hY)] with i hi he
    let N:=i.1;let p:=i.2; let s:=clim A k; let r:=mag A b k;let y:=mag A a k;let m:=width A a k
    let T:=Y N p d;let R:= ladd C r k N p d T;let R':= ladd C y k N p d T; let B':= Perch.bill e s; have hB :1 ≤ B':= costed _ _ hE
    have hY' : y*B'=r:=by unfold B' r y; rw [mag_bill,mag_bill];change Perch.bill _ s * _=Perch.bill b s; rw [overlap]; congr 1; unfold e; ring
    let P':=weightTag C d B'; have hF:R v=R' (P' v):=by unfold R; rw [← hY']; exact horse ..
    have hK:P' v=∑ i:(C.labels.level d.val).Index, P' v i • χ i := by ext1 i; simp [Pi.single_apply,χ,eq_comm]
    let F'(i):= (P' v) i
    have hz(i):‖F' i‖ ≤ ‖v i‖* Perch.bill (e*D) s:=by
       change ‖(B':ℂ)^ _ * _‖ ≤ _; rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans hB), mul_comm ‖v i‖]
       apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply (pow_le_pow_right₀ hB ((S'.bound i).trans (Nat.le_of_lt_succ d.isLt))).trans_eq; apply Glimmer.bills
    have hk : k < N:=hi; have hN:m≤N:=(wider ..).trans ((before ..).trans hk.le)
    refine ⟨hN,(hY.early _ (Nat.le_of_lt_succ d.isLt)).trans hk.le,fun x=>?_⟩
    let L:= center C.S p hN x;let A':C.label d→ₗ[ℂ] (Config G (C.side N p)→ℂ):= (C.linearO N p d x).mk' _;let E(i):=A' (R' (χ i));let β:=C.beta N p
    have hx(i): Interior (L.chamber 0) (E i) ∧ L.rootTest β (E i)≤ Q i:= (he i).choose_spec.2 x
    change Interior _ (A' (R v))∧ L.rootTest β (A' (R v)) ≤ _
    rw [hF,hK,map_sum,map_sum]; simp_rw [map_smul]; obtain ⟨hh,hK⟩:= rooted L β (seamless H ..) Finset.univ E F' (fun i _=> (hx i).1)
    refine ⟨hh,hK.trans ?_⟩; unfold w; rw [Finset.sum_mul]; refine Finset.sum_le_sum fun i _=>?_
    exact (mul_le_mul (hz i) (hx i).2 (L.root_nonneg β (E i)) (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)).trans_eq (by dsimp only [X,e,a]; ring)
-- Balances token H.Une
open Extraction.Spin
lemma third (F:Extraction.Order)(hs:(S).RealSpin)(hn:2 ≤ n)(x:ι)(b ξ:ℝ)(hb:(P x).arc ≤ b)(t:Caps m)(ht:∀ i,t i ≤ D)(v:Ribbon (Bel C.book) t):∃ Q:ℝ,0 ≤ Q ∧ ∀ᶠ k:ℕ in atTop, ∀ Y,Poised P B H O J n z k Y→
     let W':= wok C D k b ξ Y
     let d:= Next.Rank.Station.width A (P x).arc k;let c:=Q*Perch.bill ((b-(P x).arc)*D) (clim A k)
     bulk (C:=C) (t:=t) (W'.tones ht v) F c d ∧ generous (C:=C) (t:=t) (W'.tones ht v) F c d:=by
    let d (i:Fin m):Fin (D+1):= ⟨_,Nat.lt_succ_of_le (ht i)⟩
    let a (i:Fin m)(p:Extraction.Spin.Frame):= if p.2 then
      (S).conj hs (t i) ((S).mirror hs (t i) p.1 (v i)) else (S).mirror hs (t i) p.1 (v i)
    choose Q hQ he using fun i p=> second P B H h hp O J z hZ F hn x b hb (d i) (ladder C (t i) (a i p))
    let M:= ∑ i,∑ p,Q i p; have ht'(i p): Q i p ≤ M:= (Finset.single_le_sum (fun p _=> hQ i p) (Finset.mem_univ p)).trans
       (Finset.single_le_sum (fun i _=>Finset.sum_nonneg fun p _=> hQ i p) (Finset.mem_univ i))
    refine ⟨M,Finset.sum_nonneg (fun i _=> Finset.sum_nonneg fun j _=> hQ i j),?_⟩
    filter_upwards [eventually_all.mpr (fun i=> eventually_all.mpr (he i))] with k hp Y hY X j c
    let g (u):=ripped (t:=t) (C:=C) (X.tones ht v u)
    suffices hy : ∀ᶠ u : ℕ × ℕ in F.fuse, ∀ i p, centeredBudget C (token C.book (g u i) p) c j u.1 u.2 by
       exact ⟨fun i j=>hy.mono fun _ hh=>hh i j,hy.mono fun _ hh=> YM.UVNext.StationTransfer.Ticket.permit_from _ hh⟩
    have hS : ∀ᶠ u : ℕ × ℕ in F.fuse,
       X.atCut u ⟨0,Nat.succ_pos D⟩ ((S).unit 0)= C.book.scalar 0 ∧
       (∀ i x,X.atCut u i ((S).conj hs i x)=star (X.atCut u i x))∧
         ∀ i s x,X.atCut u i ((S).mirror hs i s x)=C.book.mirrorGroup i s (X.atCut u i x) := (w_right ξ F hs b hY).2
    filter_upwards [hS,eventually_all.mpr (fun i=> eventually_all.mpr fun p=> hp i p Y hY)] with u hu hh i q
    have hW:token C.book (g u i) q=⟨t i,X.atCut u (d i) (a i q)⟩:=by
      obtain ⟨i',b'⟩:= q; have ht:=hu.2.2 (d i); have hQ:= hu.2.1 (d i)
      cases b' <;> simp only [token, g,ripped,Wheel.tones,Register.move, Register.conjugate,a,Bool.false_eq_true, ↓reduceIte] <;> congr 1
      · exact (ht _ _).symm
      symm; exact (hQ _).trans (congr_arg star (ht _ _))
    rw [hW]; exact fixup C (hh i q) (mul_le_mul_of_nonneg_right (ht' i q) (Real.exp_pos _).le)
end YM.MergeProof.East
