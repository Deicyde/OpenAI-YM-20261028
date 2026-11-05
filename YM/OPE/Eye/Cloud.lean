import YM.OPE.Eye.Fleeting
import YM.Extraction.Round
/-!
# Cartesian slice of a lattice grid with projection ties removed

Same scaled interpolation for all arities; enables extension from generic
configurations without norm-continuity assumptions on ground algebra,
and without splitting a phase selection inside an integral. Nodes on
a one-dimensional component for interpolation are exactly equally spaced;
*every* choice is jointly generic for the full grid of choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cloud
open Set Function Filter Matrix MeasureTheory Lattice RG Finset WithLp Extraction
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {I : Type}[Fintype I][DecidableEq I]{J : Type}[Fintype J]
    (W : Finset E4) (z : ℝ) (hz:0<z)(x : I→E4)(n m:ℕ) (i j:I) (a:Axis)
def count (I:Type)[Fintype I](W:Finset E4):ℤ:= (Fintype.card I+1)*(W.card+1)
def block (W:Finset E4)(i:I):ℤ:= ((runNames I|>.symm i).val:ℤ)*(W.card+1)
lemma count_pos : 0< count I W:=by unfold count; positivity
lemma block_pos : 0 ≤ block W i:=by unfold block; positivity
lemma block_small : block W i+W.card < count I W := by
    unfold block count; have h : (↑(runNames I|>.symm i).val:ℤ) < Fintype.card I:= by exact_mod_cast (runNames I|>.symm i).isLt
    have ht := mul_le_mul_of_nonneg_right (show _+(1:ℤ) ≤ _ from Int.add_one_le_of_lt h) (show 0 ≤ (↑W.card:ℤ)+1 by positivity); linarith only [ht,Nat.cast_nonneg (α:=ℤ) W.card]

def bad (I:Type)[Fintype I] (W:Finset E4)(z:ℝ)(a:Axis) : Finset ℤ := W.image fun y=> ⌊y a/z⌋ % (count I W) -- I not in type; must param
lemma attain_residue : ∃ j ∈ Set.Icc (block W i) (block W i + W.card), j ∉ bad I W z a := by
    let k:= block W i; have h : (bad I W z a).card < (Finset.Icc k (k+W.card:ℤ)).card:=by calc
        _ ≤ W.card := Finset.card_image_le
        _ < _ := by rw [Int.card_Icc]; omega
    obtain ⟨j,hl,hx⟩ := Finset.exists_mem_notMem_of_card_lt_card h; exact ⟨j,Finset.mem_Icc.mp hl,hx⟩
def residue : ℤ := (attain_residue W z i a).choose
lemma residue_band : residue W z i a ∈ Set.Icc (block W i) (block W i + W.card) ∧ residue W z i a∉ bad I W z a:= (attain_residue W z i a).choose_spec
lemma residue_nonneg : 0 ≤ residue W z i a:= le_trans (block_pos ..) (residue_band ..).1.1
lemma residue_small : residue W z i a < count I W:= lt_of_le_of_lt (residue_band ..).1.2 (block_small ..)
lemma residue_inj : Injective (fun i:I=> residue W z i a):= by
    let f:= (runNames I).symm; have hx (i j:I)(h:(f i).val < (f j).val) : residue W z i a < residue W z j a:= by
       apply lt_of_le_of_lt (residue_band ..).1.2; apply lt_of_lt_of_le _ (residue_band ..).1.1
       have hp : (↑(f i).val:ℤ)< (f j).val:= by exact_mod_cast h
       have ht := mul_le_mul_of_nonneg_right (show _+(1:ℤ) ≤ _ from Int.add_one_le_of_lt hp) (show 0 ≤ (↑W.card:ℤ)+1 by positivity); unfold block; linarith only [ht]
    intro i j h; apply f.injective; apply Fin.ext; exact le_antisymm (le_of_not_gt (fun g=> (hx j i g).not_ge h.le)) (le_of_not_gt (fun g=> (hx i j g).not_ge h.ge)) -- edit

local notation "K" => count I W
local notation "r" => residue W z

def wheel : ℤ := ⌊x i a/(z*K)⌋
def node (i:I)(a:Axis)(j:ℕ) := ((wheel W z x i a+j)*count I W) + residue W z i a

def grid (α: I → Axis→ℕ) (i : I) : Cover:= fun a=> node W z x i a (α i a)
def placeGrid (α: I → Axis→ℕ) (i : I) : E4:= toLp 2 (fun j=>z*grid W z x α i j)

variable (α : I→ Axis → ℕ)
lemma node_mod : node W z x i a n % K = residue W z i a := by rw [node, Int.add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (residue_nonneg ..) (residue_small ..)] -- name
lemma placeG (S:Schedule)(k:ℕ) : S.gridPoint k ∘ grid W (S.a k) x α= placeGrid W (S.a k) x α:=rfl
lemma stride : z*(node W z x i a n)= z*(node W z x i a 0)+(n:ℝ)*(z*K):=by unfold node; push_cast; ring
include hz
lemma screened : Screen (placeGrid W z x α) := by
    intro a i j h; have he : z*(node W z x i a (α i a))= z*(node W z x j a (α j a)):=h
    have hp : node W z x i a (α i a)=node W z x j a (α j a):= by exact_mod_cast mul_left_cancel₀ hz.ne' he
    exact residue_inj W z a (by dsimp only; rw [← node_mod W z x (α i a) i a,← node_mod W z x (α j a) j a,hp])
lemma clears : ∀ y∈W, placeGrid W z x α i a≠ y a := by
    intro y hy h; apply (residue_band W z i a).2; refine mem_image.mpr ⟨_,hy,?_⟩; rw [← h]; change ⌊(z*(node W z x i a (α i a)))/z⌋ % _ = _; rw [mul_div_cancel_left₀ _ hz.ne',Int.floor_intCast,node_mod]
lemma close_zero : |z*node W z x i a 0 - x i a| ≤ z*K:= by
    let u:= x i a; let d : ℝ:= z*K; have hK:=count_pos (I:=I) W; have h : 0<d:= by unfold d; positivity
    have ht : (wheel W z x i a:ℝ)≤ u/d:= Int.floor_le _
    have he : u/d< wheel W z x i a+1:= Int.lt_floor_add_one _
    have hr : 0≤(r i a:ℝ):=by exact_mod_cast residue_nonneg W z i a
    have hr' : (r i a:ℝ)<K:=by exact_mod_cast residue_small W z i a
    rw [abs_le]; unfold node; push_cast; have h₁:= (le_div_iff₀ h).mp ht; have h₂:= (div_lt_iff₀ h).mp he; unfold d u at *; constructor <;> linarith only [h₁,h₂,mul_nonneg hz.le hr,mul_lt_mul_of_pos_left hr' hz]
lemma nearby (H:∀ i a,α i a ≤ n) : ∀ i a, |placeGrid W z x α i a-x i a| ≤ (1+n:ℝ)*(z*K) := by
    intro i a; change |z*_ - _| ≤_; unfold grid; rw [stride]; have h₁:= abs_le.mp (close_zero W z hz x i a); have hk:= count_pos (I:=I) W; have he := mul_le_mul_of_nonneg_right (show (↑(α i a):ℝ)≤ n by exact_mod_cast H i a) (show 0 ≤ z*K by positivity)
    rw [abs_le]; constructor <;> linarith only [h₁.1,h₁.2,he,show (0:ℝ) ≤ (↑(α i a):ℝ) * (z*K) by positivity]
omit hz

def unitGrid (Q:Schedule)(k:ℕ) (W:Finset E4)(x:I→E4) : I→E4 := Q.gridPoint k ∘ grid W (Q.a k) x (fun _ _=>0)
lemma gridded (Q:Schedule): Tendsto (fun i=> unitGrid Q i W x) atTop (𝓝 x):=by
    have hx : Tendsto (fun i=> Q.a i * count I W) atTop (𝓝 0):=by simpa only [zero_mul] using Q.shrinks.mul_const (↑(count I W):ℝ)
    apply tendsto_pi_nhds.mpr; intro i; -- PiLp usage
    let l : E4 ≃L[ℝ] (Axis→ℝ):= PiLp.continuousLinearEquiv 2 ℝ _; apply Tendsto.comp (f:=fun j=> l (unitGrid Q j W x i)) (g:=l.symm) (l.symm.continuous.tendsto (l (x i)))
    refine tendsto_pi_nhds.mpr fun a=> ?_; apply tendsto_iff_dist_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall (fun i=> dist_nonneg)) ?_ hx; exact Eventually.of_forall (fun p=>close_zero W (Q.a p) (Q.a_pos p) x i a)
lemma beside_tends {φ:Type*}{f:Filter φ}{x:I→E4}{y:J→E4}{z:φ→ I→ E4}{z':φ→ J→ E4}(h:Tendsto z f (𝓝 x))(he:Tendsto z' f (𝓝 y)): Tendsto (fun i=> beside (z i) (z' i)) f (𝓝 (beside x y)):= tendsto_pi_nhds.mpr fun i=> by cases i; exacts [tendsto_pi_nhds.mp h _, tendsto_pi_nhds.mp he _]
end YM.OPE.Cloud
