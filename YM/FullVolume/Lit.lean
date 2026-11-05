import YM.FullVolume.Silent
import YM.FullVolume.Stand
import YM.MergeProof.Powder

/-! # Uniform rank detection (whole mesh × every volume) -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells Next.Rank Next.Rank.Market Push.RelayDifference
open Next.Extract MergeProof
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge}{C:Family G}{S:Table C.book}{d : ℕ}{Y:Columns C S d} (T:Y.Trials) (M:C.Makes)(B:Stock.Tabs C.path.levels)(hp: Wcmain C) (h:VitalRank T)
    (V:∀ d,Source.SectionData (C.labels.level d))(R:Push.Mark.Weave G)(hV: ∀ d:ℕ,Push.Mark.Portfolio C.params (V d) (R d))
    {P:∀ d,Cutoffs→ (C.label d≃ₗ[ℂ] C.label d)} (a: Presentation C){ζ:ℕ→ℕ→ℝ}(hf:Hearthside C V R P a ζ)

include M B V R hf hV
lemma sweep (x:Bid.Rowe C d)(hx:Coin C x)(he:∀ i, a.step d i (x i)=0): Owed (Bid.upper C x) (flight C (-(1/32))):=by
   obtain ⟨p,q,h⟩:=hf.hearth d
   exact banked M B (V d) R (hV d) _ h _ hx fun i=> ((hf.foundation.step d i.1 i.2).ker) ▸ (show x i∈LinearMap.ker (a.step d i).toLinearMap from LinearMap.mem_ker.mpr (he i))

omit M B hV in
lemma weighed (i:Cutoffs): Module.finrank ℂ (LinearMap.range (a.step d i).toLinearMap) ≤ Y.dim+1:=by
   let v:= bindP C R d i.1 i.2 (P d i)
   let F:= C.labels.level d
   let T:= Maxwell.freeTable C.labels; let U:= Maxwell.equationIdeal G d
   have hg : T.null d=U.map F.coords.toLinearMap:=by
      ext x; obtain ⟨j,rfl⟩:= F.coords.surjective x
      change F.coords j∈ T.null d ↔ _
      have hh : F.coords j∈T.null d ↔ j∈U:= by
        have H := Maxwell.projectionExact C.labels (c:=F.coords j)
        rw [Extra.FD.no_residual] at H
        refine H.symm.trans ?_; simp only [Submodule.mem_bot]; constructor
        · intro h; apply LinearMap.mem_ker.mpr
          have hh : Maxwell.observable G d ((C.labels.level d).coords.symm (F.coords j))=0 := congr_arg Subtype.val h
          rw [F.coords.symm_apply_apply] at hh; exact hh
        intro h; apply Subtype.ext
        change Maxwell.observable G d ((C.labels.level d).coords.symm (F.coords j))=0; rw [F.coords.symm_apply_apply]; exact h
      rw [hh]; exact ⟨fun hi=> ⟨j,hi,rfl⟩,fun ⟨k,h,hj⟩=> F.coords.injective (show F.coords k=F.coords j from hj) ▸ h⟩
   have he := LinearEquiv.finrank_eq (v.submoduleMap U)
   have hz := LinearEquiv.finrank_eq (F.coords.submoduleMap U)
   have ha : Module.finrank ℂ (T.Field d)+Module.finrank ℂ (T.null d) = Module.finrank ℂ (C.label d):= (T.null d).finrank_quotient_add_finrank
   have hb : Module.finrank ℂ (LinearMap.ker (a.step d i).toLinearMap) = Module.finrank ℂ U:= (congrArg (fun W : Submodule ℂ (C.label d) => Module.finrank ℂ W) (hf.foundation.step d i.1 i.2).ker).trans he.symm
   have hz' : Module.finrank ℂ (T.null d)=Module.finrank ℂ U:=
      (congrArg (fun W : Submodule ℂ (C.label d)=> Module.finrank ℂ W) hg).trans hz.symm
   have hK : Module.finrank ℂ (T.Field d)=Y.dim+1:= (Module.finrank_eq_card_basis Y.basis).trans (Fintype.card_fin _)
   have hx:= LinearMap.finrank_range_add_finrank_ker (a.step d i).toLinearMap
   rw [hz',hK] at ha; rw [hb] at hx; exact (Nat.add_right_cancel (hx.trans ha.symm)).le
include T hp h

abbrev display (x : Bid.Rowe C d)(i:Cutoffs):= a.step d i (x i)
lemma trained (l:List Axis):
    ∀ᶠ k:ℕ in atTop, ∀ᶠ b:ℝ in 𝓝[>] 0, ∃ Z:ℝ,0≤Z ∧ ∀ᶠ i in mesh,∀ x:C.label d,
        ‖a.step d i x‖ ≤ Z *‖probe T k i b l (a.step d i x)‖:=by
  obtain ⟨δ,L,hd,hL,hZ⟩:= firm (true_lower Y); let ε:= δ/4; have hε:0<ε:=div_pos hd (by norm_num)
  obtain ⟨A,hA⟩:= hf.uniform d; have hAp:0≤A:= (norm_nonneg _).trans (hA (0,0))
  filter_upwards [h.performance ε hε] with k hk
  obtain ⟨v,hv⟩:= h.shops.bounded k
  have hwp : 0 ≤ v:= (norm_nonneg _).trans (hv 0 0 0)
  filter_upwards [probesUp T M hp l h.shops hε k, invites T M hp l h.shops k] with b hb hB
  let X j i:= T.lift k (Prod.fst i) (Prod.snd i) j
  let F i:= probe T k i b l; let Y' := A*(Y.dim+1:ℕ)*v*L
  have hY : 0≤Y' :=by unfold Y'; positivity
  refine ⟨Y',hY,?_⟩
  have hx j:Tendsto (fun i=> F i (X j i-display a (boostsAt T k j) i)) mesh (𝓝 0):=by
    let s := display a (boostsAt T k j); let x:Bid.Rowe C d:= boostsAt T k j - s
    have hc: ∀ i,x i=X j i-display a (boostsAt T k j) i:= fun _=> rfl
    have hC: Coin C (boostsAt T k j):= Coin.from_bound M (A:=v) (Eventually.of_forall fun i=> hv i.1 i.2 j)
    have hs: Coin C s:= Coin.from_bound M (A:=A*v) (Eventually.of_forall fun i=>
      ((a.step d i).le_opNorm _).trans (mul_le_mul (hA i) (hv _ _ j) (norm_nonneg _) hAp))
    have he : Owed (Bid.upper C x) (flight C (-(1/32))) := by
      apply sweep M B V R hV a hf x (hC.sub hs); intro i; change a.step _ _ (_ - a.step _ _ _) = _; rw [map_sub,a.projected, sub_self]
    simp_rw [← hc]; unfold F; simp_rw [probe_eq T k _ b l x]; exact hB.2 _ _ he (flown (by norm_num))
  filter_upwards [hk,hb,eventually_all.mpr (fun j=> (hx j|>.norm).eventually (gt_mem_nhds (show ‖(0:Fin Y.amount→ℂ)‖ < ε by simpa using hε)))] with i hi hv' hh x
  let f (j:Fin (Y.dim+1)) := X j i; let Z := (F i).comp ((a.step d i).toLinearMap.comp (arrange f))
  apply rank_upper (a:=a.step d i) (f:=f) (hv i.1 i.2) (hA i) hL.le (F i) (hZ Z ?_) (weighed V R a hf (Y:=Y) i) hwp x
  intro j
  have hu: Z ((Pi.basisFun ℂ _) j)=(F i) (display a (boostsAt T k j) i) := by unfold Z; rw [LinearMap.comp_apply, LinearMap.comp_apply, ordered_at]; rfl
  rw [hu]
  let v:= display a (boostsAt T k j) i
  have hd' : ‖F i (f j)- F i v‖ ≤ ε:= by
    have he := hh j
    rw [← map_sub]; exact le_of_lt he
  apply (pi_norm_le_iff_of_nonneg hd.le).mpr; intro k'
  let w := fun i=> monitor (siblings T k k') i (Bid.upper C (boostsAt T k j)) (loc T k k' i)
  have hx : ‖F i (f j) k'-w i‖ ≤ ε := by rw [← dist_eq_norm]; exact hv' k' j
  have ht : ‖w i-focus (X:=Y) k' j‖ < ε:= by rw [← dist_eq_norm]; exact hi k' j
  have hb': ‖F i v k'- F i (f j) k'‖ ≤ ε:= le_trans (norm_le_pi_norm (F i v-F i (f j)) k') (by rwa [norm_sub_rev])
  change ‖F i v k'-focus k' j (X:=Y)‖ ≤ δ
  apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ (F i (f j) k') _)
  have hy:= norm_sub_le_norm_sub_add_norm_sub (F i (f j) k') (w i) (focus k' j (X:=Y))
  dsimp only [ε] at *; linarith only [hy,ht,hx,hb',hd]
end YM.FullVolume
