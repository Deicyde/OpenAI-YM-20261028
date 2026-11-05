import YM.AnalyticBridge.VERIFIED_RESET_STEP.Comparison
import YM.Progress.DIRECTED_RECIPE.Fittings

/-! Domain continuity through fill/finish; the further subsequences here
are on parameters at fixed depth ONLY. Retain actual address/threshold
selection even through the solution on a singleton interval. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection
open Function Filter Set Lattice Wilson RG RG.Shoot Ovens Quotes Residual WilsonStartup Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ : ℝ}
    {X : Listing G n}

private lemma sec_series {ι : Type*} (f : ι → ℝ) (h : Summable f) : Summable fun i : Seat n × ι => f i.2 :=
    Summable.of_norm ((summable_prod_of_nonneg fun i : Seat n × ι => norm_nonneg (f i.2)).mpr ⟨fun _ => h.norm,Summable.of_finite⟩)
private lemma drop {ι : Type*} (f : ι → ℝ) (l : ι → ℕ) {e : ℝ} (he : 0 ≤ e) (h : ∀ i, 0 ≤ f i) (hf : Summable fun i => f i*Real.exp (e*l i)) :
    Summable f := hf.of_nonneg_of_le h fun i => le_mul_of_one_le_right (h i) (Real.one_le_exp (mul_nonneg he (by positivity)))
lemma quote_series (hx : R.Bounds c σ C Λ) (hw : Width p c σ) (α Δ : ℝ) {e : ℕ → ℝ} (he : Summable e) :
    Summable (quoteE R (n:=n) p c α Δ e) ∧ Summable (quoteL R (n:=n) p c α Δ e) := by
  have hs := hx.width
  have hl := drop (fun i : Low => |i.mark R c| * lowCost G p (i.length R)) _ (half_pos hs).le
    (fun _ => mul_nonneg (abs_nonneg _) (low_nonneg ..)) (low_budget G p R hx).2.1
  have hh := drop (fun i : High => i.price R p) _ (half_pos hs).le (fun i => i.price_nn ..) (high_budget G p R hx).2.1
  have ht := drop (fun i : Low => Real.exp ((i.length R:ℝ)/c.relaxation)* |i.mark R c|) _ (show 0 ≤ 3*σ/4 by positivity) (fun _ => by positivity)
    (kept_debit G p R hw hx).2.1
  exact ⟨Summable.sum _ (he.mul_left _) (Summable.sum _ ((sec_series _ hl).mul_left _) ((sec_series _ hh).mul_left _)),
    Summable.sum _ (he.mul_left _) ((sec_series _ ht).mul_left _)⟩

abbrev brew (X : Listing G n) (R : PathData G) (c : Clip) (p : BudgetPoint) (a : ℝ → Source G n) (α : ℝ) := fun y => branch X R c p (a y) α
namespace Compared
variable {a : ℝ → Source G n} {T : Set ℝ} {H w : ℝ → ℝ}
    (g : G.Simple) (L : ∀ x∈T, Local X p (a x) (H x) (w x)) (h : Compared X p a T)
    (hx : R.Bounds c σ C Λ) (hc : Decent c p) (hw : Width p c σ) (hn : 20 < n.val)
include g L hx hc

omit g L hx hc in
private lemma shorten {ε : ℝ} (he : 0 ≤ ε) (F : ℝ) : ε/(1+|F|)*F ≤ ε := by
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 1+|F|)]; nlinarith only [he, mul_le_mul_of_nonneg_left (le_abs_self F) he]

include h hn in
lemma flow (α : ℝ) : Flow p (brew X R c p a α) (shelves X R p) T := by
  let Q := brew X R c p a α
  apply Progress.DirectedRecipe.Flow.mk (d:=Q)
  · intro x he i ε hε
    let F := quoteE R p c 0 1 (fun _ => 1) (numbering (EKey n) i)
    filter_upwards [h.quote_at g L hx hc α hn x he (ε/(1+|F|)) (by positivity)] with y hy
    obtain ⟨_,hh⟩ := hy.1 i
    exact ⟨hε.le,fun U hU l hl hL => (hh U hU l hl hL).trans (shorten hε.le F)⟩
  refine Payments.steady (T:=T) (d:=Q) (fun x hx' i => ?_) (fun x hx i => ⟨?_,(h.values x hx).2 i⟩) p
  · obtain ⟨u,hu,_⟩ := (L x hx').cheap
    exact ⟨_,fun U => Local.quote_soft (v:=a x) (R:=R) (c:=c) g α _ hu (L x hx').smooth (numbering _ i) U⟩
  intro ε hε
  let F := quoteL R p c 0 1 (fun _ => 1) (numbering (LKey n) i)
  filter_upwards [h.quote_at g L ‹R.Bounds c σ C Λ› hc α hn x hx (ε/(1+|F|)) (by positivity)] with y hy U
  exact (hy.2 i U).trans (shorten hε.le F)

include hw in
lemma comparison (α : ℝ) {s : Set ℝ} {e k : ℕ → ℝ} {B : ℝ}
    (hs : s.Nonempty) (ht : s ⊆ T) (he : Summable e) (hk : Summable k) (hm : ∀ x∈s, Majorizes p e k (X.read (a x)))
    (hB : ∀ x∈s, |Averaging.delta (X.read (a x))| ≤ B) :
    PreBound p (brew X R c p a α) (shelves X R p) s := by
  let v := quoteE R (n:=n) p c |α| B e; let f := quoteL R (n:=n) p c |α| B e
  let t := brew X R c p a α
  have hQ := quote_series (n:=n) hx hw |α| B he
  have hh (y : ℝ) (hy : y∈s) : let Δ := Averaging.delta (X.read (a y)); |α+Δ| ≤ 1*(|α|+B) ∧ |Δ| ≤ 1*|B| := by
    simp only [one_mul]; exact ⟨(abs_add_le ..).trans (by linarith [hB y hy]),(hB y hy).trans (le_abs_self B)⟩
  have h0 : 0 ≤ B := by obtain ⟨y,hy⟩ := hs; exact (abs_nonneg _).trans (hB y hy)
  have hA := abs_of_nonneg (add_nonneg (abs_nonneg α) h0)
  refine Payments.pre_finite (p:=k) (q:=f ∘ numbering _) hs hk ((numbering _).summable_iff.mpr hQ.2) (fun x hx' i U => ⟨(hm x hx').hard i |>.2 U, ?_⟩)
    ⟨v ∘ numbering _,(numbering _).summable_iff.mpr hQ.1,fun x hx' i => ?_⟩
  · refine (Local.quote_soft (v:=a x) (R:=R) (c:=c) g α _ (hm x hx').smooth (L x (ht hx')).smooth (numbering _ i) U).trans ?_
    change quoteL .. ≤ f (numbering _ i); rcases numbering (LKey n) i with j|⟨z,d⟩
    · rfl
    simpa only [f,v,quoteE,quoteL,Sum.elim_inr,Sum.elim_inl,one_mul] using L_dominate (R:=R) (p:=p) (c:=c) (Sum.inr (z,d)) (le_refl (0:ℝ)) (hh x hx').1 (hh x hx').2 hA.symm
  refine sup_le (Local.quote_regular (v:=a x) g hx hc α _ (hm x hx').smooth (L x (ht hx')).smooth (numbering _ i)) ?_
  change quoteE .. ≤ v (numbering _ i); rcases numbering (EKey n) i with j|⟨z,d⟩|⟨z,d⟩
  · rfl
  · simpa only [f,v,quoteE,quoteL,Sum.elim_inr,Sum.elim_inl,one_mul] using E_dominate (R:=R) (p:=p) (c:=c) (Sum.inr (Sum.inl (z,d))) (le_refl (0:ℝ)) (hh x hx').1 (hh x hx').2 hA.symm
  simpa only [f,v,quoteE,quoteL,Sum.elim_inr,Sum.elim_inl,one_mul] using E_dominate (R:=R) (p:=p) (c:=c) (Sum.inr (Sum.inr (z,d))) (le_refl (0:ℝ)) (hh x hx').1 (hh x hx').2 hA.symm

open Samples
include h hw in
lemma selected (α : ℝ) {x : ℝ} (h' : x∈T) (s : ℕ → ℝ) (hs : ∀ j,s j∈T) (hh : Tendsto s atTop (𝓝 x)) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ PreBound p (brew X R c p a α) (shelves X R p) (sample x (s ∘ r)) := by
  have ht := within hs hh
  obtain ⟨r,e,k,hr,he,hk,hw',hQ⟩ := h.series x h' s ht
  let B y := |Averaging.delta (X.read (a y))|
  obtain ⟨m,hm⟩ := eventually_atTop.mp ((ht.comp hr).eventually (h.drifting g L h' zero_lt_one) |>.and hQ)
  let R j := r (j+m)
  obtain ⟨v,hv,hM⟩ := strictMono_subseq_of_tendsto_atTop (u:=R) (hr.comp (tendsto_atTop_mono (show id ≤ (· + m) from fun j => Nat.le_add_right j m) tendsto_id))
  refine ⟨R ∘ v,hM, comparison g L hx hc hw α (insert_nonempty ..) (sample_sub h' (fun i => hs _)) he hk ?_
    (B:=B x+1) ?_⟩
  · intro y hy; rcases hy with (rfl|⟨j,rfl⟩)
    · exact hw'
    exact (hm (v j + m) (Nat.le_add_left ..)).2
  intro y hy; rcases hy with (rfl|⟨j,rfl⟩)
  · exact le_add_of_nonneg_right zero_le_one
  have hA := (hm (v j + m) (Nat.le_add_left ..)).1
  exact le_trans (by simpa using abs_sub (Averaging.delta (X.read (a x))) (Averaging.delta (X.read (a x)) - Averaging.delta (X.read (a (s (R (v j)))))))
    (add_le_add le_rfl hA)

include h hw hn in
lemma completed {β θ : ℝ → ℝ} (α : ℝ) {δ γ : ℝ → ℝ} (hβ : ContinuousOn β T) (hθ : ContinuousOn θ T)
    (hF : ∀ x∈T,Fees G p c σ C α (H x) (w x) (δ x) (γ x)) : Curve p (fun x => finish R c p (shelves X R p) (branch X R c p (a x) α) (β x) (θ x)) T := by
  let t := brew X R c p a α; let X' := shelves X R p
  have hh x hx' := (L x hx').renew g hx hc hw α hn (hF x hx')
  refine { beta := ?_, v := ?_, reg := ?_, forced := ?_, continuous := ?_ }
  · change ContinuousOn β T; exact hβ
  · change ContinuousOn θ T; exact hθ
  · intros; change (drawer G n).reg = _; rfl
  · intros; change Ovens.Pipes.addr (folio G n) p = _; rfl
  intro ε hε x hT
  let f y := Ovens.Pipes.fused (folio G n) p (Rack.widen X' (t y))
  change ∀ᶠ y in 𝓝[T] x, deviation p (f x) (f y) ε
  by_contra h'
  obtain ⟨s, hs,ht⟩ := exists_seq_forall_of_frequently ((not_eventually.mp h').and_eventually (show ∀ᶠ y in 𝓝[T] x,y∈T from self_mem_nhdsWithin))
  have hs' := hs.mono_right nhdsWithin_le_nhds
  obtain ⟨r,hr,hR⟩ := h.selected g L hx hc hw α hT s (fun j => (ht j).2) hs'
  have hy := sample_sub hT fun i => (ht (r i)).2
  let J := X'.encoding.some
  obtain ⟨j,hj⟩ := ((within (sample_map x _) (hs'.comp hr.tendsto_atTop)).eventually
    (((h.flow g L hx hc hn α).tighter hy).measured hR J (mem_insert ..) ε hε)).exists
  obtain ⟨κ₁,ν₁,u₁,H₁,_⟩ := (hh x hT).pays; obtain ⟨κ₂,ν₂,u₂,H₂,_⟩ := (hh (s (r j)) (ht _).2).pays
  exact (ht _).1 ((lift_fused H₁ J).compares (lift_fused H₂ J) hj)
end Compared
end YM.AnalyticBridge.VerifiedReset.Collection
