import YM.Contacts.Normal.Subtractions

/-! # Fixed finite-seminorm accounting for normal tests

Can pay for maps into a parameter space (where testing or differentiating jointly). Requests are
only at finite lists of jet orders. No threshold dependence on requiring successively finer shells.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory MultipleContact Panel
open scoped Topology BigOperators Classical ContDiff
variable {E F G : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup G][NormedSpace ℝ G]
variable {U V : Set E}{n j i : ℕ}{f g : E → F}{t s r d : ℝ}

structure Jet (n : ℕ)(U : Set E)(f : E→F)(r : ℝ) : Prop where
  pos : 0 ≤ r
  bounds (i : ℕ) : i ≤ n → ∀ x∈U, ‖iteratedFDeriv ℝ i f x‖ ≤ r
lemma le_inf_order (i : ℕ) : (i:WithTop ℕ∞) ≤ (∞:WithTop ℕ∞) := by exact_mod_cast (show (i:ℕ∞)≤⊤ from le_top)
lemma controls (hf : ContDiff ℝ ∞ f) (h : IsCompact U) (i : ℕ) : ∃ B ≥ (1:ℝ), Jet i U f B := by
  choose A hA using fun j : Fin (i+1) => h.exists_bound_of_continuousOn (hf.continuous_iteratedFDeriv (le_inf_order j.val)).continuousOn
  obtain ⟨B,hb⟩:=Finite.bddAbove_range A; let t:=max 1 B; refine ⟨t,(le_max_left ..), le_trans zero_le_one (le_max_left ..),fun k hk x hx=>?_⟩
  let j:Fin (i+1):=⟨k,by omega⟩; exact (hA j x hx).trans ((hb (Set.mem_range_self j)).trans (le_max_right ..))
namespace Jet
lemma enlarge (h : Jet n U f r)(he:r ≤ t)(hv : V ⊆ U)(hh : i ≤ n) : Jet i V f t := ⟨h.pos.trans he,fun j hj x hx=> (h.bounds j (hj.trans hh) x (hv hx)).trans he⟩
lemma mono (h : Jet n U f r)(he : r ≤ t) : Jet n U f t := h.enlarge he (by rfl) le_rfl
lemma weaker (h : Jet n U f r) (he : j ≤ n) : Jet j U f r := h.enlarge le_rfl (by rfl) he
lemma value (h : Jet n U f r) {x : E} (he : x∈ U) : ‖f x‖ ≤ r:= by simpa only [norm_iteratedFDeriv_zero] using h.bounds 0 (Nat.zero_le _) x he
lemma sub (h : Jet n U f r) (k : Jet n U g d) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : Jet n U (f-g) (r+d) := by
  refine ⟨add_nonneg h.pos k.pos, fun i hi x hx=>?_⟩; rw [iteratedFDeriv_sub_apply (lowerSmooth hf _|>.contDiffAt) (lowerSmooth hg _|>.contDiffAt)]; exact (norm_sub_le ..).trans (add_le_add (h.bounds i hi x hx) (k.bounds i hi x hx))
lemma plus (h : Jet n U f r) (k : Jet n U g d) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : Jet n U (f+g) (r+d) := by
  refine ⟨add_nonneg h.pos k.pos, fun i hi x hx=>?_⟩; rw [iteratedFDeriv_add_apply (lowerSmooth hf _|>.contDiffAt) (lowerSmooth hg _|>.contDiffAt)]; exact (norm_add_le ..).trans (add_le_add (h.bounds i hi x hx) (k.bounds i hi x hx))
lemma scalar (h : Jet n U f r) (hf : ContDiff ℝ ∞ f)(s : ℝ) : Jet n U (fun i=>s • f i) (|s| * r):= by
  refine ⟨mul_nonneg (abs_nonneg _) h.pos, fun i hi x hx=>?_⟩; rw [iteratedFDeriv_const_smul_apply' (lowerSmooth hf _|>.contDiffAt),norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (h.bounds i hi x hx) (abs_nonneg _)
lemma join {I : Type*} (L : Finset I) (p : I → E→F) {S : I→ℝ} (h : ∀ i∈L, Jet n U (p i) (S i)) (hs : ∀ i,ContDiff ℝ ∞ (p i)) : Jet n U (fun t=>∑ i∈L,p i t) (∑ i∈L,S i) := by
  induction L using Finset.induction_on with
  | empty => simp_rw [Finset.sum_empty]; exact ⟨le_rfl, fun i _ x _=> by simp⟩
  | insert i L hi ih => simp_rw [Finset.sum_insert hi]; exact (h i (by simp)).plus (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj)) (hs i) (ContDiff.sum fun j _=> hs j)
lemma times {f g:E→ℂ} (h : Jet n U f r) (k : Jet n U g d)(hf : ContDiff ℝ ∞ f)(hg : ContDiff ℝ ∞ g) : Jet n U (f*g) (((2:ℝ)^n)*r*d):=by
  have h0:=h.pos; have h1:=k.pos
  refine ⟨by positivity, fun i hi x hx=>?_⟩; apply (norm_iteratedFDeriv_mul_le hf hg x (le_inf_order i)).trans
  calc
    _ ≤ ∑ j∈Finset.range (i+1),(i.choose j:ℝ)*r*d := Finset.sum_le_sum fun j hj=> by
            gcongr
            · exact h.bounds _ (le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hi) x hx
            exact k.bounds _ (by omega) x hx
    _ ≤ _ := by rw [← Finset.sum_mul,← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow,Nat.cast_ofNat]; gcongr; norm_num
lemma compose {g : F→ G} (h : Jet n U f r) (k : Jet n univ g d) (hr : 1 ≤ r)(hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : Jet n U (g ∘ f) ((n.factorial:ℝ)*d*r^n):=by
  have h0:=h.pos; have h1:=k.pos; refine ⟨by positivity, fun i hi x hx=>?_⟩;
  refine (norm_iteratedFDeriv_comp_le hg hf (le_inf_order i) x (D:=r) (fun j hj=> k.bounds j (hj.trans hi) _ (Set.mem_univ _)) (fun j hj hkv=> (h.bounds j (hkv.trans hi) x hx).trans (?_))).trans (?_)
  · conv_lhs=> rw [← pow_one r]
    exact pow_le_pow_right₀ hr hj
  gcongr

lemma recover (h : Jet n U f r) (he : tsupport f⊆ U) : Jet n univ f r:= by
  refine ⟨h.pos,fun i hi x hx=>?_⟩; by_cases hp:x∈U; exact h.bounds i hi x hp
  rw [notMem_support.mp (show x∉Function.support (iteratedFDeriv ℝ i f) from fun hw=> hp (he (support_iteratedFDeriv_subset _ hw))),norm_zero]; exact h.pos
lemma near (h : Jet n U f r)(hg : ∀ x∈ U, f =ᶠ[𝓝 x] g) : Jet n U g r := by
  refine ⟨h.pos, fun i hi x hx=>?_⟩; rw [← ((hg x hx).iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds]; exact h.bounds i hi x hx

lemma priceBlade {f : E→ℂ} (L: List E)(hf : ContDiff ℝ ∞ f)(h : Jet i U f r)(hi : L.length ≤ i){x : E} (hx : x∈U) :
      ‖blades L f x‖ ≤ r*(L.map (‖·‖)).prod:= by
  let v:=L.get; have hv:List.ofFn v=L:=List.ofFn_get L; have ht:= iteratedFDeriv ℝ L.length f x|>.le_opNorm v
  nth_rw 1 [← hv, blades_eval hf]; refine ht.trans (mul_le_mul (h.bounds _ hi _ hx) (le_of_eq (?_)) (Finset.prod_nonneg (fun i _=>norm_nonneg _)) h.pos)
  calc _ = (List.ofFn (fun i=> ‖v i‖)).prod := List.prod_ofFn.symm
       _ = _:= congrArg List.prod (show List.ofFn (fun i=> ‖v i‖)=(L.map (‖·‖)) from by change List.ofFn (norm ∘ v)=_; rw [← List.map_ofFn,hv])
end Jet
end YM.Contacts.Normal
