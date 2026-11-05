import YM.RG08.Quire.Beats
/-!
# Normalized Fk conditional mark: output equality after expansion in BOTH density & source law
Retain the zero-mark denominator, before any scalar read.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Quire
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff BigOperators
variable {α X : Type} [Fintype X] [DecidableEq X] {M : Matrix X X ℝ}
variable {L n : ℕ}
private lemma rim_sound {F : Op X} (h : Muted _ F) (e : Fluid F) (W : Op X) : rim M W (priori F)=dancing (rim M W F) (priori F) := by
  rw [rimD,rimD,sing_a]; simp_rw [sing_a,dance_price,dance_rotate,sway_exp _ e h]
lemma dance_fluid {F W : Op X} (h : Fluid F) (hp : Fluid W) : Fluid (dancing F W) := by
  intro i j; unfold dancing; simp_rw [Finset.sum_fn]; exact ContDiff.sum fun u _=> ContDiff.sum fun v _=>(h _ _).mul (hp _ _)
private lemma wick_play {F W : Op X} (h : Fluid F)(hp : Fluid W)(he : Mᵀ=M) : landP M (dancing W F)= dancing (landP M W) F+dancing W (landP M F) + rim M W F := by
  funext n e
  have hh (b : ℕ×ℕ)(a : ℕ×ℕ) : ContDiff ℝ ω (W b.1 a.1 * F b.2 a.2) := (hp _ _).mul (h _ _)
  have hx b : ContDiff ℝ ω (∑ a∈wheel e, W (b:ℕ×ℕ).1 a.1 * F b.2 a.2) := by simp_rw [Finset.sum_fn]; exact ContDiff.sum (fun i _=> hh b i)
  unfold landP rim dancing; rw [lap_sum (s:=wheel n) (h:=fun i _=>hx i)]; simp_rw [lap_sum _ (wheel e) (fun i _=>hh _ i),lap_joint _ he (hp _ _) (h _ _),sum_add_distrib]; rfl
lemma hymn_Mark {S W : Op X} (hg : Fluid S)(hf : Fluid W)(hm : Muted _ S)(he : Mᵀ=M) (hv : Views M S)(hw : countT W=landP M W + rim M W S) : countT (dancing W (priori S))=landP M (dancing W (priori S)) := by
  rw [wick_play (priori_fluid hg) hf he,rim_sound hm hg,countTn,hw,dance_plus,heat_priori M hm hg hv]; abel
omit [Fintype X] [DecidableEq X] in
def singing (L : ℕ) (F : Op X) : Prop := ∀ i j, windows L j < i → F i j=0
omit [Fintype X] [DecidableEq X] in
def furnace (L : ℕ) (F : Op X) (e : ℕ) : Psalm X := ∑ i∈range (windows L e+1), F i e
omit [Fintype X] [DecidableEq X] in
def billow (F W : Reel (Psalm X)) (e : ℕ) := ∑ p∈wheel e,F p.1*W p.2
private lemma rises {F W : Op X} (h : tempered _ F) (hv : singing L W) : singing L (dancing W F) := by
  intro i j he; apply sum_eq_zero; intro a ha; apply sum_eq_zero; intro b hb; have h₁:= mem_antidiagonal.mp ha; have h₂:=mem_antidiagonal.mp hb; by_cases hz:windows L b.1<a.1; · rw [hv _ _ hz,zero_mul]
  rw [h a.2 b.2 (by unfold terrace; unfold windows at *; omega),mul_zero]
private lemma rate_one {F W : Op X} (h : tempered _ F)(hv : singing L W) : furnace L (dancing W F)=billow (furnace L W) (tempo 1 F) := by
  funext i; unfold furnace dancing billow
  have hx j : ∑ b∈wheel j,∑ a∈wheel i, W b.1 a.1 * F b.2 a.2=∑ a∈wheel i,∑ b∈wheel j, W b.1 a.1 * F b.2 a.2:= sum_comm
  simp_rw [hx]; rw [sum_comm]; refine sum_congr rfl fun a ha=>?_; symm
  have he := mem_antidiagonal.mp ha
  simp only [furnace,tempo,one_pow,one_smul]; rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
  exact Eq.trans (triangle_sum (fun j k=> W j a.1 * F k a.2) (windows L a.1) (terrace a.2) (fun x y hk=>⟨Nat.lt_add_one_iff.mpr
     (le_of_not_gt fun hT=> hk (by rw [hv _ _ hT,zero_mul])), Nat.lt_add_one_iff.mpr (le_of_not_gt fun ht=> hk (by rw [h _ _ ht,mul_zero]))⟩)) (by rw [show windows L a.1+terrace a.2=windows L i from by unfold windows terrace; omega])

def emitter (L : ℕ) (M : Matrix X X ℝ) (T U : Reel (Psalm X)) := furnace L (fun n e=>wickLayer M n (billow U (expEra T) e))
lemma candle {F W : Op X} (hF : Muted _ F) (hf : tempered _ F) (hg : Fluid F) (he : Fluid W) (hm : Mᵀ=M) (hw : Views M F) (hb : singing L W) (hx : countT W=landP M W+rim M W F) :
    emitter L M (F 0) (W 0)=billow (furnace L W) (cloud M (F 0) 1) ∧ singing L (fun n e=>wickLayer M n (billow (W 0) (expEra (F 0)) e)) := by
  let P := priori F
  have hu : countT (dancing W P)=landP M (dancing W P) := hymn_Mark hg he hF hm hw hx
  have hv : (priori F 0)=expEra (F 0) := aura_exp_unique (aura_unit_era (rhythm_exp _) hF) (aura_starts (hF _))
  have ha : billow (W 0) (expEra (F 0))=dancing W P 0 := by rw [← hv]; exact funext fun i=> (dance_crown W P i).symm
  have hP : (fun n e=> wickLayer M n (billow (W 0) (expEra (F 0)) e))=dancing W P := by
    rw [ha]; exact funext fun n=> funext fun e=> (wick_eq_n M _ hu (dance_fluid he (priori_fluid hg)) n e).symm
  unfold emitter; rw [hP]; constructor
  · rw [rate_one (priori_timing hf) hb]
    unfold cloud; rw [← hv]
    congr 2; exact funext fun i=> funext fun j=> wick_eq_n M _ (heat_priori M hF hg hw) (priori_fluid hg) i j
  exact rises (priori_timing hf) hb
end YM.RG08.Quire
end
noncomputable section
namespace YM.RG08.Quire
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix
open scoped Topology ContDiff BigOperators
variable {α : Type} [Fintype α] [DecidableEq α] {m : Side} {L : ℕ}
variable {U : Screed ℝ α} {M : Row α α} {S : Canticle α}
theorem denominator (i : Site m) (h : Whole M)(he : (M.acts m)ᵀ=M.acts m) (hk : ∀ i j,Tunable (S i j))(hw : Decked S)(hv : ∀ i j,Tidy (U i j))(hu : Fits L U) :
    let F e := grand (e+2) (S e) m
    let Q e := grand (e+2) (upswell M S (some m) 1 e) m
    let inmark e := large i (L+e) (U e)
    let outmark e := large i (L+e) (washed L (some m) M S U e)
    Aura (cloud (M.acts m) F 1) Q ∧ emitter L (M.acts m) F inmark=billow outmark (cloud (M.acts m) F 1) ∧
      singing L (fun n e=> wickLayer (M.acts m) n (billow inmark (expEra F) e)) := by
  intro F Q inmark outmark
  refine ⟨log_wells h hw hk m 1 |>.1,?_⟩
  obtain ⟨hg,hb,hp⟩:= pendants i h hk hw hv hu
  obtain ⟨hF,hM,hT,hS,-⟩:= head_beats (m:=m) h hk hw
  have hZ := candle hM hT hF hg he hS (L:=L) hb hp
  rw [show F= Beats M S m 0 from ?_,show inmark=vault i L U M S 0 from ?_,show outmark=furnace L (vault i L U M S) from ?_]; exact hZ
  · funext e; unfold outmark large washed; simp_rw [root_sum _ _ _ (fun j _=>quiet_tidily h hk hv _ _ _ _|>.pens)]; exact sum_comm
  · funext e; unfold inmark vault large; simp_rw [murmur]
  funext e; unfold F Beats grand; simp_rw [Refrain]
end YM.RG08.Quire
