import YM.WilsonBulk.Tickets.Issue

/-!
# Cost of a literal invariant completion correction, without asking the RG space for any curvature lift

We use this in two histories with NO A0 difference estimates. All rows pass
with full colors, only the head applied to the plume even at finite mesh.
Height gathered over ALL nonroot legs in native units. Stage cost polynomial
once width gate chosen below 1 (as well as later heat/cross demands).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Sheet
open scoped Topology Classical BigOperators ENNReal
open Function Filter Equiv Finset Lattice Pert.Bulk AnalyticNext
variable {X : Type} {D : Rule X} {σ θ C M : ℝ} {p q d k n : ℕ} {V : Page X (n+1)} {P : Page X n}

def shutters (T : Legs (X≃X) n) : Legs X n≃Legs X n:= Equiv.piCongrRight T
lemma shutters_at (t : Legs (X≃X) n) (x : Legs X n) (i : Fin n) : shutters t x i=t i (x i):= rfl
lemma shove_cost (T : Legs (X≃X) n) (hp : ∀ i x,D.cost x (T i x) ≤ C)
    (x : Legs X n) (i : Fin n) : run D (x i) x≤run D (T i (x i)) (shutters T x)+2*n*C := by
  unfold run
  calc
   _ ≤ ∑ j : Fin n,(2*C+D.cost (T i (x i)) (shutters T x j)) := sum_le_sum (fun j _=> by
          rw [shutters_at]; linarith only [D.tri (x i) (T i (x i)) (x j), D.tri (T i (x i)) (T j (x j)) (x j), D.swap (x j) (T j (x j)), hp i (x i), hp j (x j)])
   _ = _ := by simp [Finset.sum_add_distrib,nsmul_eq_mul]; ring
lemma shove (T : Legs (X≃X) n) (hp : ∀ i x,D.cost x (T i x) ≤ C)
    (h : Within D σ M P) (hs : 0 ≤ σ) (he : σ ≤ 1) (hk : 0 ≤ C) :
    Within D σ (M*Real.exp (2*n*C)) (P ∘ (shutters T:Legs X n→ Legs X n)) := by
  let e:= Real.exp (2*n*C); have hx:= h.1
  refine ⟨by positivity,fun i x=> ?_⟩; rw [ENNReal.ofReal_mul hx]; refine LE.le.trans ?_ (mul_le_mul_left (h.2 i (T i x)) _)
  unfold rent; rw [← ENNReal.tsum_mul_right, ← (shutters T).tsum_eq (fun v=> (if v i=T i x then bill (P v) (σ*run D (T i x) v) else 0)* ENNReal.ofReal e)]
  apply ENNReal.tsum_le_tsum; intro y; dsimp only [Function.comp_apply]; rw [shutters_at]; split_ifs with H K K
  · rw [← show bill 1 (2*n*C)=ENNReal.ofReal e from by unfold e bill; rw [abs_one,one_mul], ← purchase,mul_one]; refine bill_mono le_rfl ?_
    rw [← H]; have ht:= Nat.cast_nonneg (α:=ℝ) n; linarith only [mul_le_mul_of_nonneg_left (shove_cost T hp y i) hs, mul_le_mul_of_nonneg_right he (show 0≤(2*n*C) from by positivity)]
  · exact (K (congr_arg _ H)).elim
  all_goals exact bot_le

lemma Within.postage (h : Within D θ M V) (u : Equiv (Fin n) (Fin k)) : Within D θ M (Parapet.postage u V) := by
  let A := (Equiv.optionCongr u); let v:Equiv (Fin (n+1)) (Fin (k+1)):= (finSuccEquiv n).trans (A.trans (finSuccEquiv k).symm)
  have hp : Parapet.postage u V=escort v V := by
    funext z; rw [Parapet.postage, Parapet.castTail]; unfold Sheet.escort margin; refine congr_arg V ?_; ext1 i
    cases i using Fin.cases <;> simp [v,A,crop]
  rw [hp]; exact h.reindex v
lemma Within.tail_clean (h : Within D θ M V) : Within D θ M (Parapet.tailBuff V) := by
  let p : ℝ:= (Fintype.card (Grouping n):ℝ); have hp : 0 < p:= by unfold p; positivity
  rw [show Parapet.tailBuff V=p⁻¹ • ∑ i:Grouping n, Parapet.postage i V from ?_]
  · refine ((Within.sum (univ:Finset (Grouping n)) fun x _=> h.postage x).scale p⁻¹).mono le_rfl (Eq.le ?_); rw [sum_const,card_univ,nsmul_eq_mul]; rw [abs_of_nonneg (by positivity : 0≤p⁻¹)]; change p⁻¹ * (p*M)=_; field_simp
  apply Parapet.margin_force; intro x; simp only [Parapet.postage,Parapet.tailBuff,Parapet.margin_scale,Parapet.margin_grabs, Parapet.post_mark]; rfl
end Sheet
namespace Parapet
open Function Filter Lattice Laurent RG Equiv Finset Exterior Pert.Bulk Atelier Wilson Sheet
open scoped Topology Classical BigOperators ENNReal
variable {G : Gauge} {n k q d e r : ℕ} {σ θ M H : ℝ} {V : Text (Cloth G) (n+1)}

def remotePlace (t : Bool) (a : PotentialForm) : Cover:= backed t a 0
lemma backed_price (x : Cover) (t a) : backed t a x=x+remotePlace t a := by cases t <;> simp [remotePlace,backed, sub_eq_add_neg]
variable (t : Bool) (a : PotentialForm) (u i : G.ColorIndex)
def closureMove : Legs (Mark G≃Mark G) (n+1) := hitch (prodCongr (Equiv.addRight (remotePlace t a)) (Equiv.swap (coord 0,i) (a,u))) (fun _=>Equiv.refl _)
lemma closure_height (j : Fin (n+1)) (x : Mark G) :
    (lawn (Cloth G)).cost x ((closureMove t a u i) j x) ≤ length (remotePlace t a) := by
  cases j using Fin.cases
  · rw [closureMove,hitch_zero]; change length (x.1- (x.1+_)) ≤_; rw [show x.1- (x.1+_)= -(remotePlace t a) from by abel,length_neg] -- maybe wrong
  rename_i j; change sep x.1 ((((closureMove t a u i) j.succ) x).1) ≤_ -- inspect
  rw [closureMove,hitch_succ,Equiv.refl_apply,sep_self]; show 0 ≤ (_:ℝ); positivity
variable (v : Legs G.ColorIndex k)
def patchTail (i : G.ColorIndex) := hitch ((0:Cover),coord 0,i) (selvedge (cameo backed t a 0) ∘ v)
lemma patch_equal (x : Mark G) (y : Legs (Mark G) k) (p : x.2=(coord 0,i)) :
    hitch x y= roll (x.1-(patchTail t a v i 0).1) (Cloth G) ∘ patchTail t a v i ↔ y=selvedge (cameo backed t a x.1) ∘ v := by
  have ht : roll x.1 (Cloth G) ∘ (selvedge (cameo backed t a 0) ∘ v)=selvedge (cameo backed t a x.1) ∘ v := by
    ext1 j; unfold selvedge cameo; simp only [Function.comp_apply, roll_apply]; rw [backed_price,zero_add,backed_price]; congr 1; abel
  unfold patchTail; simp only [hitch_zero, sub_zero, hitch_comp,ht]
  rw [show roll x.1 (Cloth G) ((0:Cover),coord 0,i)= x from Prod.ext (zero_add _) p.symm]; exact ⟨fun h=> by have H:=congr_arg crop h; simpa using H, congr_arg (hitch x)⟩
lemma patch_fits (x : Mark G) (y : Legs (Mark G) k) : hairs (patchTail t a v i) 1 (hitch x y)=(if x.2=(coord 0,i) ∧ y=selvedge (cameo backed t a x.1) ∘ v then 1 else 0) := by
  rw [hair_pin (patchTail t a v i) 1 _ 0]; by_cases hh:x.2=(coord 0,i)
  · simp only [hitch_zero, patch_equal t a i v _ _ hh,hh,true_and]
  simp only [hh,false_and,↓reduceIte]; rw [if_neg]; intro h; exact hh (congr_arg Prod.snd (congr_fun h 0))
lemma plume_here (V : Text (Cloth G) (n+1)) : plume backed t a u i v V= seam (V ∘ (shutters (closureMove t a u i : Legs (Mark G≃Mark G) (n+1)))) (hairs (patchTail t a v i) 1) := by
  funext w; let e:=shutters (closureMove t a u i : Legs (Mark G≃Mark G) (n+1)); let T:=seam (V ∘ e) (hairs (patchTail t a v i) 1)
  refine legs_succ (fun w : Legs (Mark G) (n+k+1)=> plume backed t a u i v V w=T w ) (fun x z=> ?_) w
  refine legs_plus (fun z=> plume backed t a u i v V (hitch x z)=T (hitch x z)) (fun y z=> ?_) z
  unfold T; rw [seam_apply,patch_fits]; unfold plume castTail; rw [hitch_zero,crop_hitch]; dsimp only
  split_ifs with H K L
  · rw [tassel_pay,if_pos K.2,mul_one]; change V _= V _; congr 1; ext1 j; cases j using Fin.cases
    · rw [hitch_zero]; unfold e; rw [shutters_at,hitch_zero,closureMove,hitch_zero]; exact Prod.ext (backed_price ..) (by change _ = Equiv.swap _ _ x.2; rw [H, Equiv.swap_apply_left]; rfl)
    rw [hitch_succ]; rfl
  · rw [tassel_pay, if_neg (fun h=>K ⟨H,h⟩),mul_zero]
  · exact (H L.1).elim
  simp

def pluckPay (n : ℕ) := Real.exp (2*(n+1)*length (remotePlace t a))* ribs 1 1 (patchTail t a v i)
lemma plume_width (hv : Within (lawn (Cloth G)) σ M V) (he : σ ≤ 1) (h : 0 ≤ θ) (hs : 0 ≤ σ)
    (hk : ((k:ℝ)+1)*θ ≤ σ) (hn : ((n:ℝ)+1)*θ ≤ σ) :
    Within (lawn (Cloth G)) θ (pluckPay t a i v n * M) (plume backed t a u i v V) := by
  rw [plume_here]; refine (Within.sewn (shove _ (closure_height t a u i) hv hs he (by positivity)) ((hairs_within (patchTail t a v i) 1 1).mono he le_rfl) h hk hn).mono le_rfl (Eq.le ?_)
  unfold pluckPay; push_cast; ring
-- same t,a,i,u consumed inside finite grammar. Count generic with EPOCH no schedule.

def rippleCash (G : Gauge) (n k : ℕ) := ∑ t:Bool, ∑ a:PotentialForm,∑ i:G.ColorIndex,∑ u:G.ColorIndex,∑ v:Legs G.ColorIndex k, |shaft t u i v| * pluckPay t a i v n
lemma ripple (hv : Within (lawn (Cloth G)) σ M V) (he : σ ≤ 1) (h : 0 ≤ θ) (hs : 0 ≤ σ)
    (hk : ((k:ℝ)+1)*θ ≤ σ) (hn : ((n:ℝ)+1)*θ ≤ σ) :
    Within (lawn (Cloth G)) θ (rippleCash G n k * M) (spiro backed V k) := by
  unfold spiro ribbons; apply Within.tail_clean; unfold rippleCash; simp_rw [Finset.sum_mul, mul_assoc]
  exact Within.sum _ fun t _=> Within.sum _ fun a _=> Within.sum _ fun i _=> Within.sum _ fun u _=> Within.sum _ fun v _=> (plume_width t a u i v hv he h hs hk hn).scale _
-- strict predecessor width cap before L. θcoarse/L ≤ pulseUse by length choices

def pulseGrow (θ : ℝ) (n : ℕ) := θ*(n+1)
def stakeRate (G : Gauge) (e n i : ℕ) := if i+1 ≤ e ∧ i+1 ≤ n then
   |((n-(i+1)+1:ℕ):ℝ)| * rippleCash G (n-(i+1)) (i+1) else 0

def knee (G : Gauge) (e n : ℕ) := |(-( ((n+1:ℕ):ℝ)⁻¹ ))| * ∑ i∈range e, stakeRate G e n i
lemma pulse_cost {I : Library G}
    (h : Whisper I) (hs : σ ≤ 1) (hp : pulseGrow θ n ≤ σ) (he : 0 ≤ θ) (hz : 0≤ σ) (hv : ∀ i:ℕ, 0 < i → i≤e → i≤n → Within (lawn (Cloth G)) σ M (I (e-i) (n-i+1))) :
    Within (lawn (Cloth G)) θ (knee G e n * M) (diss backed (I e (n+1))) := by
  rw [submission h e n, knee, mul_assoc, sum_mul]; refine (Within.sum _ fun i hx=>?_).scale _; by_cases hk:i+1≤e ∧ i+1≤n
  · rw [proceeding, dif_pos hk, stakeRate, if_pos hk,mul_assoc]; refine ((ripple (hv (i+1) (by omega) hk.1 hk.2) hs he hz ?_ ?_).postage _).scale _ <;> apply LE.le.trans ?_ hp <;> unfold pulseGrow <;> rw [mul_comm θ] <;> gcongr <;> omega
  rw [proceeding, dif_neg hk, stakeRate, if_neg hk, zero_mul]; exact Within.zero le_rfl
lemma knee_nn (G : Gauge) (e n : ℕ) : 0≤ knee G e n := by
  have h i : 0≤stakeRate G e n i:= by
    unfold stakeRate; split
    · apply mul_nonneg (abs_nonneg _); refine sum_nonneg fun p _=> sum_nonneg fun _ _=> sum_nonneg fun _ _=> sum_nonneg fun _ _=> sum_nonneg fun _ _=> mul_nonneg (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le (ribs_nonneg ..))
    rfl
  exact mul_nonneg (abs_nonneg _) (sum_nonneg fun i _=> h i)
end Parapet
end YM.WilsonBulk
