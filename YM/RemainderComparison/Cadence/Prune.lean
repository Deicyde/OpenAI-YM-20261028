import YM.RemainderComparison.Cadence.Pending
import YM.RemainderComparison.Quartz.Frozen
/-! # p2 true fallback packets. `core` is whole MAIN (curved, incl high unclip in α)
 not yet a legal cap cohort! -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cadence
open Function Filter Metric Set Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure PhysicalNext.Repeat Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange Next.Scheduling ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Sienna Fare Germ Token Aux Portal Merge Palette Cascade Lyric Lotus Marker Next.Rank.Glyph Next.Rank.Exponential
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {r j n k N m : ℕ} {Z σ C D W A v u d e t a c' B' c₀:ℝ}
variable {c f : Side} {S : StepData c f} {ι : Type} {α : Type}
variable {T : Tube G S} (F : Forest S.ratio) {Θ : ChartRatio G} (k': S.Choices) (ρ:Bid.Dir G c→AxisChart G F) (B V:BudgetPoint) (β:ℝ)
local notation "Xs"=> Positions (Uniform.Primary c G)
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "θ"=> Lapis.orbit F ρ
local notation "g"=> gStep β
variable {x:Positions (Uniform.Primary c G)} {K:KernelChoices} {O:Teller G} {R:Rep G f}
open Herbal
variable (P:PathData G) (q:Clip)(α₁ W' :ℝ)
def edict (U:Config G c):= α₁*mainTerm q P U+ Precision.loop P U
def sprigs (P:PathData G) (q:Clip) (X:ℝ) (G':ℝ): Eden c G (Fin 3):= ⟨univ,![0,0,2],![2,0,0],![-mainTerm q P,-edict P q X,fun _=>G']⟩
-- Vertical polynomial interpretation incl scalar at origin. no tie.G.geometries.
local notation "V'"=> sprigs P q α₁ W'
local notation "H₁"=> (fun i:ℝ×Xs=> mainTerm q P (Herbal.sail F (Aux.nod F ρ i)))
local notation "H₂"=> (fun i:ℝ×Xs=> edict P q α₁ (Herbal.sail F (Aux.nod F ρ i)))
lemma peaceful : aria F ρ V'= (-Trace.pending (H₁) 1-H₂) + fun x:ℝ×Xs=> x.1^2*W':=by
     funext x; unfold aria; rw [show ((sprigs (c:=c) P q α₁ W').ground)=(Finset.univ : Finset (Fin 3)) from rfl, Fin.sum_univ_three]; change x.1^0 • Trace.pending (-H₁) 1 x+ x.1^0 • (-H₂ x)+x.1^2 • W'= _; rw [pow_zero,one_smul,one_smul,Trace.negative]; simp [sub_eq_add_neg]
lemma peel (hB:0<β) (U:Config G c) : (V').groups β U= -(β* mainTerm q P U)- edict P q α₁ U + g^2*W':=by
    unfold Eden.groups; rw [show ((sprigs (c:=c) P q α₁ W').ground)=(Finset.univ : Finset (Fin 3)) from rfl, Fin.sum_univ_three]; change ((g)^0 * ((g)^2)⁻¹*(-mainTerm q P U)+(g)^0*((g)^0)⁻¹*(-edict P q α₁ U))+ (g)^2*((g)^0)⁻¹ * W'= _
    have he: ((g)^2)⁻¹=β:= by unfold gStep; rw [inv_pow,inv_inv,Real.sq_sqrt hB.le]
    rw [he]; ring
section terrain
variable (t':ℕ→Atom G m) (ha:SumBudget (fun i=>(t' i).budget σ) C) (hX:∀ i,(t' i).Invariant)
variable (hσ: 0<σ) (hp:0 ≤ Z)
def floral (A σ Z X:ℝ)(G:Gauge)(k m:ℕ):ℝ:= A*(X*(1+prize k m G σ Z))
local notation "K₁"=> floral (Fintype.card (Site c)) σ Z C G k
include hσ hp ha hX
lemma fair (s:Signed) : Sect (fun U:Config G c=> uncut t' (pull s 0 U)) B.threshold m k Z (K₁ m):= by
   have he (i:Site c): Sect (Herbal.club t' (fun _=>i) (fun _=>1) (fun _=>s)) B.threshold m k Z (C*(1+prize k m G σ Z)) := Herbal.aSect _ _ _ _ hσ (by simpa only [abs_one,one_mul]) B hp hX -- refine syntax check
   have h:= Herbal.array Finset.univ _ _ (fun i _=>he i)
   unfold Herbal.club at h; simp_rw [one_mul,sum_const,card_univ,nsmul_eq_mul] at h
   exact h
omit ha hX
include hσ hp
private lemma fancy (X:ℝ)(h:0 ≤ X) : 0≤ floral (Fintype.card (Site c)) σ Z X G k m:=by
   unfold floral; exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg h (zero_le_one.trans (le_add_of_nonneg_right (prizes_pos hp hσ))))
omit hσ hp
lemma warm {P : Config G c →ℝ} (he:Sect P B.threshold j k Z C) (h:0≤ C) (hu:B.threshold≤1) (hx:m≤ j): Sect P B.threshold m k Z C:= by
   refine ⟨⟨he.tall,@fun E _ _ U hU=> ⟨(he.mode E U hU).1, fun i hx' hi=> (he.mode E U hU).2 _ hx' (hi.trans_le hx)⟩⟩,he.vigor,he.localM,fun U hc=>(he.value U hc).trans ?_⟩
   exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one B.threshold_pos.le hu hx) h
open Oriented
variable (hP:P.Bounds q σ C D)
local notation "Vp"=> Fintype.card (Face (Per c)) * Quartz.stipend G σ C q k Z
include hp hP
lemma since (h:B.threshold≤1) : Sect (mainTerm q P (n:=c)) B.threshold 2 k Z ((Vp + K₁ 3)+ K₁ 4):= by
    -- per-channel
    let H:= Classical.choose_spec (Herbal.considerable G σ C Z k)
    have hv (s:Signed):Sect (fun U:Config G c=>quadratic q P (pull s 0 U)) B.threshold 2 k Z (Vp):= by
      have hy:=(Herbal.array Finset.univ _ (fun _=>Quartz.stipend G σ C q k Z) (fun i _=> Herbal.authorize (f:=c) B P q hP s i H.2))
      simpa only [sum_const,card_univ,nsmul_eq_mul] using! hy
    let N :ℝ:= (Vp + K₁ 3)+K₁ 4
    have hc:0≤ C:= (tsum_nonneg hP.three.1).trans hP.three.2.2
    let A':ℝ:=(Fintype.card Signed); have ha':0<A':=Nat.cast_pos.mpr Fintype.card_pos
    have hk (s:Signed): Sect (fun U: Config G c=> (quadratic q P (pull s 0 U) + uncut P.cubic (pull s 0 U))+uncut P.quartic (pull s 0 U)) B.threshold 2 k Z N := Herbal.merge (Herbal.merge (hv s) (warm B (fair B _ hP.three (fun i=>(hP.invariant i).2.1) hP.width hp s) (fancy hP.width hp _ hc) h (by omega))) (warm B (fair B _ hP.four (fun i=>(hP.invariant i).2.2) hP.width hp s) (fancy hP.width hp _ hc) h (by omega))
    have ht:= Herbal.grow (Herbal.array univ _ (fun _=>N) (fun s _=>hk s)) (A'⁻¹)
    rw [Finset.sum_const,nsmul_eq_mul,card_univ,Real.norm_of_nonneg (inv_pos.mpr ha').le,show (Fintype.card Signed:ℝ)=A' by rfl, inv_mul_cancel_left₀ ha'.ne'] at ht; exact ht

local notation "Nc"=> Vp + K₁ 3 + K₁ 4
local notation "Hm"=> floral (Fintype.card (Site c)) σ Z D G k 2
lemma quest (h:B.threshold≤1) : Sect (edict P q α₁ (c:=c)) B.threshold 0 k Z (‖α₁‖*Nc+Hm):= by
   have he:0 ≤ D:= (tsum_nonneg hP.two.1).trans hP.two.2.2
   have hc:0 ≤ C:= (tsum_nonneg hP.three.1).trans hP.three.2.2
   let A := (Fintype.card Signed:ℝ); have hh:0<A:= Nat.cast_pos.mpr Fintype.card_pos
   have ht:= Herbal.grow (Herbal.array univ _ (fun _=>Hm) (fun s _=>fair B _ hP.two (fun i=>(hP.invariant i).1) hP.width hp s)) (A⁻¹)
   rw [Finset.sum_const,nsmul_eq_mul,card_univ,Real.norm_of_nonneg (inv_pos.mpr hh).le,show (Fintype.card Signed:ℝ)=A by rfl,inv_mul_cancel_left₀ hh.ne'] at ht
   have hC:0≤Nc:= add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Quartz.decent ..)) (fancy hP.width hp _ hc)) (fancy hP.width hp _ hc)
   exact Herbal.merge (Herbal.grow (warm B (since B P q hp hP h) hC h (Nat.zero_le _)) α₁) (warm (P:=Precision.loop P) B ht (fancy hP.width hp _ he) h (Nat.zero_le _))
lemma jetset (hs:3 ≤ N)(h:B.threshold≤1)(hh:Nc≤v)(ha: ‖α₁‖*Nc+ Hm ≤ v) (ht:‖W'‖ ≤ v) : Eden.Culture (sprigs P q α₁ W' (c:=c)) N k B.threshold Z v 0:= by
   let hp₁:= Herbal.climbed (since B P q hp hP h) B.threshold_pos.le hh; let hp':= Herbal.climbed (quest B P q α₁ hp hP h) B.threshold_pos.le ha
   refine ⟨by simpa only [sprigs,card_univ,Fintype.card_fin], fun i _=> ⟨?_,?_,?_⟩,(norm_nonneg _).trans ht,fun _ _=> Nat.cast_nonneg _⟩
   · fin_cases i <;> (first|change 0 ≤ N | change 2 ≤ N) <;> omega -- fix
   · fin_cases i <;> (first | change 2 ≤ N | change 0 ≤ N) <;> omega
   fin_cases i
   · change Sect (-(mainTerm q P (n:=c))) _ 2 k _ _
     simpa only [norm_neg,norm_one,one_mul,neg_one_mul] using! Herbal.grow hp₁ (-1)
   · change Sect (-(edict P q α₁ (c:=c))) _ 0 k _ _
     simpa only [norm_neg,norm_one,one_mul,neg_one_mul] using! Herbal.grow hp' (-1)
   refine ⟨⟨fun E _ _ U hU y _=>(Brush.certified zero_le_one (x:=y) (k:=k) W').climb ht le_rfl,fun E _ _ U hU=> ⟨contDiffAt_const,fun i hx' hi=> False.elim (Nat.not_lt_zero i hi)⟩⟩,fun _ _=> rfl,measurable_const,fun U _=>?_⟩
   change ‖W'‖ ≤ v*B.threshold^0; rwa [pow_zero,mul_one]
end terrain
end YM.RemainderComparison.Cadence
