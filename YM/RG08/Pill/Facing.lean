import YM.RG08.Door.Conseil
/-!
# Taut algebra of frame units along independent reset trajectories. All exact.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Pill
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Matrix Summit PertExtension.Series.Tested PertExtension.Series.Radial Scores PowerSeries Door
open scoped BigOperators Topology Real ContDiff
variable {X:Chain}{G:Gauge}{E e N r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings Summit
local notation "⨯" => (PowerSeries.X:PowerSeries ℝ)
local notation "Z" => ladder X ν D' N
lemma stencilSub (a f:PowerSeries ℝ) (n:ℕ): coeff n (PowerSeries.subst (⨯*a) f)= ∑ i∈range (n+1),coeff i f * coeff (n-i) (a^i) := by
    let V (A:PowerSeries ℝ): Cues:=fun i=>coeff i A; have h (A:PowerSeries ℝ) : PowerSeries.mk (V A)=A:= by ext i; rw [coeff_mk]
    rw [show ⨯*a=Span (V a) by rw [Span,h]]; nth_rw 1 [← h f]; rw [merge_f]; unfold powT; simp_rw [h]; rfl
lemma sorted_eq {a b:PowerSeries ℝ} (hx:coeff 1 a=1)(hp:coeff 1 b=1)(hz:a^2=b^2): a=b := by
    by_contra ht
    have he : (a-b)*(a+b)=0:= by rw [show (a-b)*(a+b)=a^2-b^2 by ring,hz,sub_self]
    have hh:= eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero.mpr ht) he
    have h : coeff 1 (a+b)=0:= by simp [hh]
    rw [map_add,hx,hp] at h; norm_num at h
lemma look (N i k) : constantCoeff (ladder X ν D' N i k)=0:= by unfold ladder; simp
lemma expect (i k N:ℕ): coeff 1 (ladder X ν D' N i k)=1:= by change coeff (0+1) (_*afternoons _)=1; rw [coeff_succ_X_mul]; unfold afternoons; simp [mat_zero]
lemma notary : Z k k= ⨯:= by
  apply sorted_eq (expect ..) (by simp) _
  rw [fuel,Span, full_at,mul_one,expand_X]
-- composition stations facing fine slot i+1 in reference k distinct view. eq incl i=0
lemma bottom : PowerSeries.subst (Z (i+1) k) (Z i (i+1))=Z i k:= by
  let a:=Z i (i+1); let b:=Z (i+1) k; let v:=Z i k
  have hz : HasSubst b:= .of_constantCoeff_zero' (look ..); have ht : HasSubst a:=.of_constantCoeff_zero' (look ..)
  have hv:HasSubst (⨯^2):= .of_constantCoeff_zero' (by simp)
  change PowerSeries.subst b a=v
  refine sorted_eq (b:=v) ?_ (expect ..) ?_ ; swap
  · let W := PowerSeries.mk (slag X ν D' N i)
    have he : ⨯ ^ 2=a^2 * PowerSeries.subst (⨯^2) W:= by
      have H:= reporting_ratio (X:=X) (ν:=ν) (D:=D') N i (i+1); dsimp only at H; rw [notary] at H; exact H
    have hh : PowerSeries.subst b (⨯^2)=b^2:= by rw [subst_pow hz,subst_X hz]
    have hQ: PowerSeries.subst b (⨯^2)= PowerSeries.subst b (a^2) * PowerSeries.subst (b^2) W:= by conv_lhs=> rw [he]; rw [subst_mul hz,subst_comp_subst_apply hv hz,hh]; rfl
    rw [hh,subst_pow hz] at hQ
    have hE : b^2=v^2 * PowerSeries.subst (b^2) W:= reporting_ratio ..
    exact mul_right_cancel₀ (show PowerSeries.subst (b^2) W ≠ (0 : PowerSeries ℝ) by
      intro h; rw [h,mul_zero] at hE; apply mt (fun H:b=0 => show coeff 1 b=0 by rw [H]; exact map_zero _) (by rw [expect ..]; simp); exact not_ne_iff.mp (fun x=> pow_ne_zero 2 x hE)) (hQ.symm.trans hE)
  · unfold b; rw [ladder,stencilSub, sum_range_succ,expect ..]; simp [afternoons,mat_zero]
lemma back (N i k): PowerSeries.subst (ladder X ν D' N i k) (ladder X ν D' N (i+1) i)=ladder X ν D' N (i+1) k := by
  let a:= ladder X ν D' N (i+1) i; let b:= ladder X ν D' N i (i+1); let c:= ladder X ν D' N (i+1) k; let d:= ladder X ν D' N i k
  have ha:HasSubst a:=.of_constantCoeff_zero' (look ..); have hb: HasSubst b:= .of_constantCoeff_zero' (look ..); have hc: HasSubst c:=.of_constantCoeff_zero' (look ..)
  have hU:IsUnit (coeff 1 a):= by rw [expect ..]; exact isUnit_one
  let q:=a.substInvOfIsUnit hU; have hA: HasSubst q:=.substInvOfIsUnit a hU; have hQ : PowerSeries.subst a b =⨯:= bottom.trans notary
  have ht:PowerSeries.subst q a= ⨯:= a.subst_substInvOfIsUnit_right (look ..) _
  have hf : q=b:= (subst_X hA).symm.trans (by rw [← hQ, subst_comp_subst_apply ha hA,ht]; simp)
  change PowerSeries.subst d a= c; rw [show d=PowerSeries.subst c b from bottom.symm,← subst_comp_subst_apply hb hc,← hf,ht,subst_X hc]
lemma global (N i j k): PowerSeries.subst (ladder X ν D' N j k) (ladder X ν D' N i j)= ladder X ν D' N i k := by
  have hz:HasSubst (ladder X ν D' N j k):=.of_constantCoeff_zero' (look ..)
  have ht i j : HasSubst (ladder X ν D' N i j):= .of_constantCoeff_zero' (look ..)
  by_cases he : j≤ i
  · induction i,he using Nat.le_induction with
    | base=> rw [notary,subst_X hz]
    | succ i hh ih=> conv_lhs => rw [←back N i j, subst_comp_subst_apply (ht ..) hz, ih]; rw [back]; rfl -- conv maybe
  · have hh:= le_of_lt (lt_of_not_ge he)
    clear he
    induction hh using Nat.decreasingInduction with
    | self=> rw [notary, subst_X hz]
    | of_succ m he ih=> conv_lhs=> rw [← @bottom X G N m j ν D',subst_comp_subst_apply (ht ..) hz,ih,bottom] -- verify @ args
end YM.RG08.Pill
