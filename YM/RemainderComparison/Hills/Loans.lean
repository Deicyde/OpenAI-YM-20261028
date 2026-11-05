import YM.RemainderComparison.Hills.Twins
import YM.RemainderComparison.Ethereal.Models
/-! # Same clipped vacuum base relationship. Pay all leaks.OXYGEN for posts. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Hills
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Geo
open Extra.Iteration WilsonStartup PhysicalNext.Repeat Song Meadow Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n C : Side} {ι : Type} (R : PathData G) (c : Clip) (p : BudgetPoint) {α:Type*}
variable {σ φ Λ A u v d a : ℝ} (β γ:ℝ)
open WickReps Musicology Animals
variable (b:α)(h:R.Bounds c σ φ Λ)(hp: WilsonStartup.Decent c p)(hw:Geo.Width p c σ)
open Ethereal Lacuna
local notation "X'"=> Hills.lyric R c p β γ n α
local notation "σt"=> p.supportExponent
open UVNext.PricedKernels Ovens
open Trio

def chanting (G:Gauge)(n:Side) : Vowel G n ℕ:= rekey (Ethereal.spare G n) (numbering _)
local notation "C'"=> chanting G n
lemma motifs : Normal (C') p ∧ (Vowel.overlay (C') p)=0 ∧ Vowel.Pricings (C') p σt 0:=by
    let A:= Ethereal.spare G n
    refine ⟨Ethereal.locking A _ _ ⟨fun i=> by exact CouplingShape.reg_const _, fun i=> rfl, fun i hi x y h₁ h₂=> ?_,?_⟩,?_,?_⟩
    · unfold logHessian; change iteratedFDeriv ℝ 2 (fun _=> (0:ℝ)) _ _=0 -- adjust
      rw [iteratedFDeriv_succ_const]; rfl
    · constructor; intro s b; refine ⟨Song.whirl s b,fun i=>?_⟩
      have he:= Song.spirit (fun (_:ℕ)=>(⟨(0:Site n),{0},Finset.mem_singleton_self _⟩:RegularAddress n)) (fun (_:ℕ) (_:Config G n)=>0) s b i
      exact ⟨(Ethereal.lineTest he.1 he.2.1).symm,rfl⟩
    · funext V; unfold Vowel.overlay; rw [show (∑' i, (C').ray p i V)= 0 from (tsum_congr (g:=fun i:ℕ=>0) (fun i=> ?_)).trans tsum_zero] -- edit
      · rfl
      unfold Vowel.ray; simp [chanting,rekey,Ethereal.spare,masked]
    exact Ethereal.sprouts _ p _ ⟨⟨0,fun _=>le_rfl⟩,⟨fun _=>0,fun i=> ⟨CouplingShape.reg_const _,Progress.DirectedRecipe.no_cost ..⟩,fun i=> budget_of_sum (fun i=> by split<;>simp) (fun s=>by simp)⟩⟩
-- earth Charge.Hiss Soft.Low lending on Healthy.L. Returns no kernel on health.When feeding post.Materials.Tips.
def sigh (d : Low) : Pot G n := d.loan R c 0 p γ 0
def whistle (s:Faces n) : Pot G n := VerifiedReset.factor • (fun V => sigh R c p γ s.2 (s.1.view V))
local notation "f₀"=> Hills.whistle R c p γ
local notation "L₀"=> numbering (Faces n)
def breeze (n:Side) : Hiss G n :=⟨fun i=> (lowEntry G R p (numbering (Faces n) i)).support,
      fun i=>⟨_,(lowEntry G R p (numbering (Faces n) i)).anchor⟩, Hills.whistle R c p γ ∘ (numbering _)⟩
local notation "Sx"=> Hills.breeze R c p γ n
local notation "Y"=> (Set.univ:Set Musicology.Void)
include h hp hw
variable (V: Config G n)
local notation "sF"=> VerifiedReset.factor

def quoteA (G:Gauge)(p:BudgetPoint)(c:Clip)(σ C γ:ℝ):= hitPower p G γ 0*lowHard p c σ C
lemma storm : (Sx).Magic p (σt+1) (quoteA G p c σ φ γ) := by
    have ht (i:Faces n) : Tidy p (lowEntry G R p i).support (f₀ i) := Trio.tidy_scale _ _ (⟨Push.Local.uses_pull (i.2.loan_reads R c 0 hp _ _) _ _, (i.2.loan_meas R c 0 p _ _).comp (continuous_pull ..).measurable,Push.Local.invariant_pull (i.2.loan_gauge R c 0 p _ _) _ _⟩: Tidy p _ (fun V=> sigh R c p γ i.2 (i.1.view V))) -- arity
    let f (i:Faces n):= hitPower p G γ 0* (Real.exp ((i.2.length R:ℝ)/c.relaxation)*|i.2.mark R c|)
    have hh (i:Faces n) (U') : ‖f₀ i U'‖ ≤ f i:=by
       change ‖sF • sigh R c p γ i.2 _‖≤_; rw [norm_smul, Real.norm_of_nonneg factor_pos.le]; exact (mul_le_of_le_one_left (norm_nonneg _) factor_le).trans ((i.2.loan_bound R c _ p γ 0 _).trans_eq (mul_assoc ..))
    have hl := hit_scale (hitPower_pos p G γ 0) (rows (n:=n) G R c p h hw|>.2.2) -- .le? check
    refine ⟨fun _=>ht _,fun i U' hc=>?_,⟨f∘ (L₀),fun i=> (norm_nonneg _).trans (hh _ 1),fun i=> Cost.equiv (L₀) (hl i),fun U i=> hh _ U⟩,fun s b=>?_⟩
    · let j:= L₀ i; change Healthy p.threshold (j.1.spread _) U' at hc; change sF* Low.loan R c j.2 0 p γ 0 (j.1.view U')=0; unfold Low.loan; rw [if_pos ((j.1.healthy ..).1 hc),mul_zero]
    let ε:= (Seat.move s b).prodCongr (Equiv.refl Low); let f:= ((L₀).trans ε).trans (L₀).symm; have he (i) : L₀ (f i) = ε (L₀ i):=(L₀).apply_symm_apply _
    refine ⟨f,fun i=>?_⟩; let j:= L₀ i
    change (lowEntry G R p (L₀ (f i))).support= _ ∧ f₀ (L₀ (f i))= _
    rw [he]; refine ⟨Seat.spread_move .., funext (fun V=> ?_)⟩; exact congr_arg (fun U=>sF * sigh R c p γ j.2 U) (congr_fun (Seat.view_move ..) V)
lemma contiguous : (Sx).canopy V = VerifiedReset.layer (sigh R c p γ) V := by
    rw [VerifiedReset.layer_total (sigh R c p γ) V (loan_sum h hw hp γ 0)]
    exact (L₀).tsum_eq (fun i=> f₀ i V)
local notation "H'"=> averaged (fun q=> ∑ i:Pressure.Cell n, R.baseTerm c p (pull q 0 V) i)
open AnalyticBridge.GaussianFieldAlignment
omit hp in
lemma spongy : VerifiedReset.layer (fun u:Low=> u.live R c p 0) V= H':=by
    let B (x:Site n) (V:Config G n):= ∑ b:PlaqAxes,R.baseTerm c p V (x,b)
    have hp' (x:Site n)(V:Config G n): B 0 (translate x V)= B x V:=by
       have hk : PathData.kept c p.threshold 0 (translate x V) ↔ PathData.kept c p.threshold x V:=by simpa only [zero_add] using! Turn.translated_kept x V p.threshold c 0
       have he : ∀ i:PlaqAxes, R.baseTerm c p (translate x V) (0,i) = R.baseTerm c p V (x,i):=by
         intro i; have ht:= Channels.translated_face x V (0,i)
         have he : Channels.shift x PlaqAxes (0,i)=(x,i):=Prod.ext (zero_add _) rfl
         have hv : R.ell (translate x V) (0,i) = R.ell V (x,i):=by
            unfold PathData.ell; apply tsum_congr; intro j; unfold PathData.ellTerms Slot.atSite; dsimp only; rw [Slide.increases]
         simp only [PathData.baseTerm,hk,ht,he,hv]
       unfold B; simp_rw [he]
    unfold VerifiedReset.layer averaged; simp_rw [show ∀ U:Config G n,(∑' i : Low, i.live R c p 0 U) = B 0 U from Low.live_total h hw 0]; apply congr_arg (sF *·)
    simp_rw [Fintype.sum_prod_type]; apply sum_congr rfl; intro s h
    rw [← Equiv.sum_comp s.actEquiv.toEquiv (fun x=>B 0 _)]
    exact sum_congr rfl fun x _=> by rw [show Seat.view (s,s.actEquiv.toEquiv x) V= translate x (pull s 0 V) from (by rw [← Lattice.pull_one,pull_pull,mul_one,affine,add_zero]; rfl),hp']
lemma gliding : γ*H'= γ* Collection.receipt R c p V+(Sx).canopy V := by
    rw [contiguous R c p γ h hp hw V,← spongy R c p h hw V, ← VerifiedReset.layer_scale,Collection.receipt, ← VerifiedReset.layer_scale, ← VerifiedReset.layer_combine]
    · apply congr_arg (VerifiedReset.layer · V); funext i W; unfold sigh; simpa [Low.fresh,masked,Set.indicator] using Low.loans_identity R c i 0 hp γ 0 W -- masked_goal
    · intro W; exact (Low.maskedPlain_sum h p 0 W).mul_left _
    intro W; exact loan_sum h hw hp ..
end YM.RemainderComparison.Hills
