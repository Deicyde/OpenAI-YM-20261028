import YM.RG08.Ward.Morning
import YM.RG08.Shade.Operas
/-!
# Formal mark Ward, all orders and separately even when reweighted.
`n≥τ`: unlike vacuum doesn't impose parity or exclude constants.
Signal calibrated at measurement, no test derivatives truncated
here; they remain passive as announced.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Loom
open Function Filter Set Lattice Wilson Exterior Bloch Next.Free Work.F08 RG Laurent Precision Finset
open Quire Stationary Scores Scores.Pages Matrix Push.AbsoluteSums PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Shade Reflect Analysis
open scoped Topology ContDiff Classical BigOperators
variable {α X : Type} {G : Gauge} {D p n r k τ ε : ℕ} {m c f L : Side} {R : ℝ}

-- isolate covariant mark **before** re-expansion.
def strand (τ q : ℕ) (U : Screed ℝ α) (r : ℕ) : Shale α r := if τ ≤ q+r then U (q+r-τ) r else 0

def GaugeNear (u v : ℝ→Link G m) := (∃ (k : ℝ→ Site m→G.El) (z : G.El), Tendsto k (𝓝 0) (𝓝 (fun _=>z)) ∧ ∀ᶠ t in 𝓝 0,input G m (v t)=gauge (k t) (input G m (u t)))
def arco (m : Side) (U : Reel (Psalm (Lines G m 1))) (v : ℝ→Link G m) (k : ℕ) := year (fun e t=> U e (v t)) k
def Shore (o : Site m) (τ : ℕ) (U : Screed ℝ (Loc G 1)) : Prop := ∀ v w:ℝ→ Link G m, AnalyticAt ℝ v 0 → AnalyticAt ℝ w 0 → GaugeNear (suitify v) (suitify w) → ∀ k : ℕ, let L e:= large o (τ+e) (U e); Fit (k+1) (arco m L v k) (arco m L w k)
def Parade (m : Side) (τ : ℕ)(U : BoardU D R G) := ∀ φ : Exam D,∀ i : Site m,Shore i τ (fun e r=> plug φ R ∘ U e r)
-- In this convention `input left` at right-transformed configuration (+ transformations of passive tests explained later).
def DiscSpin (s : Signed) (i j : Site m) (U V : Screed ℝ (Loc G 1)) := ∀ e r (v : Link G m),
    rootSong (U e r) m i v=rootSong (V e r) m j (orderTurn s v) -- infer
-- expenses implicit
lemma root_scaleX [Fintype α] (U : Shale α r) (p : ℝ) (v:PAC α m)(i : Site m): rootSong U m i (p • v)=p^r * rootSong U m i v := Tensor.homogeneous ..
-- reorganize without pad counts; `fits τ` calls later for chart.
lemma resume (m : Side) (i : Site m) (τ k : ℕ) (v : Link G m) (U : Screed ℝ (Loc G 1))(t : ℝ) :
    (∑ q∈Finset.range (k+τ+1), t^q * large i (k+τ-q) (strand τ q U) (t • v)) =
      t^τ * ∑ e∈Finset.range (k+1), t^e * large i (τ+e) (U e) v := by
  let X := Finset.range (k+τ+1)|>.sigma (fun q=> Finset.range (k+τ-q+1))
  let Y:= Finset.range (k+1)|>.sigma (fun e=>Finset.range (τ+e+1))
  let h (p : Sigma (fun _ : ℕ=>ℕ)) := t^p.1 * rootSong (strand τ p.1 U p.2) m i (t • v)
  let u (p : Sigma (fun _ : ℕ=>ℕ)) := t^τ * (t^p.1 * rootSong (U p.1 p.2) m i v)
  unfold large; simp_rw [Finset.sum_apply,Finset.mul_sum]; rw [← Finset.sum_sigma (f:=h), ← Finset.sum_sigma (f:=u)]
  let Z:= X.filter fun p=>τ ≤ p.1+p.2
  change ∑ j∈X, h j= ∑ j∈Y, u j
  rw [← show (∑ j∈Z,h j)=∑ j∈X,h j from sum_subset (filter_subset ..) fun j hj hz=>by unfold h strand; rw [if_neg (fun hh=>hz (mem_filter.mpr ⟨hj,hh⟩)),root_zero,Pi.zero_apply,mul_zero]]; symm
  have he (a b): Sigma.mk a b∈Y ↔ a≤k ∧ b≤τ+a := by simp [Y,Sigma.mk]
  have hx (a b): Sigma.mk a b∈Z ↔ (a≤k+τ ∧ b≤k+τ-a) ∧ τ≤a+b := by simp [Z,X]
  let L (i : Sigma fun _ : ℕ=> ℕ) : (Sigma fun _ : ℕ=> ℕ) := Sigma.mk (τ+i.1-i.2) i.2
  let H (i : Sigma fun _ : ℕ=> ℕ) : (Sigma fun _ : ℕ=> ℕ) := Sigma.mk (i.1+i.2-τ) i.2
  refine Finset.sum_nbij' L H ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a,b⟩ ht; change L _ ∈ Z; change Sigma.mk _ _∈Z; rw [hx]; have hU:= (he _ _).mp ht; dsimp; omega
  · rintro ⟨a,b⟩ ht; change Sigma.mk _ _∈Y; rw [he]; have hU:=(hx _ _).mp ht; dsimp; omega
  · rintro ⟨a,b⟩ ht; have hU:=(he _ _).mp ht; dsimp [H,L]; congr 1; omega
  · rintro ⟨a,b⟩ ht; have hU:=(hx _ _).mp ht; dsimp [H,L]; congr 1; omega
  rintro ⟨a,b⟩ ht; have hU := (he a b).1 ht; dsimp only [L,h,u]; unfold strand; rw [if_pos (by omega), show τ+a-b+b-τ=a by omega, root_scaleX,← mul_assoc,← mul_assoc,← pow_add,← pow_add]; congr 2; omega

variable {U V : Screed ℝ (Loc G 1)}
private lemma gauge_comp {v w : ℝ→Link G m} (h : GaugeNear v w)(f : ℝ→ℝ) (hv : Tendsto f (𝓝 0) (𝓝 0)) : GaugeNear (v∘f) (w∘f) := by obtain ⟨k,z,hk,H⟩:=h; exact ⟨k∘f,z,hk.comp hv,hv.eventually H⟩
private lemma grade_mark {I : Finset ℕ}{F H : ℕ→ℝ→ℝ} {k : ℕ} (h : ∀ i,ContDiffAt ℝ ∞ (F i) 0)(hp : ∀ i,ContDiffAt ℝ ∞ (H i) 0)
    (he : ∀ x:ℝ,Fit (k+1) (fun t=> ∑ i∈I,t^i*F i (t*x)) (fun t=>∑ i∈I, t^i*H i (t*x))) (q : ℕ)(hq:q ∈ I)(j : ℕ) (hj : j+q≤ k) : ink (F q) j=ink (H q) j := by
  let u:=j+q; let Y (F : ℕ→ℝ→ℝ) (x t : ℝ):= ∑ i∈I,t^i*F i (t*x)
  let m (F : ℕ→ℝ→ℝ) := fun i x=>(if i≤u then x^(u-i)*ink (F i) (u-i) else 0)
  have hx (F : ℕ→ℝ→ℝ) (hf : ∀ i, ContDiffAt ℝ ∞ (F i) 0) (x : ℝ) : ContDiffAt ℝ ∞ (Y F x) 0 ∧ ink (Y F x) u= ∑ i∈I, m F i x := by
    have hv i : ContDiffAt ℝ ∞ (fun t=> F i (t*x)) 0 := ((zero_mul x).symm ▸ hf i).comp (f:=fun t=>t*x) 0 (contDiffAt_id.mul contDiffAt_const)
    let z i := fun t:ℝ=>t^i* F i (t*x)
    have he i : ContDiffAt ℝ ∞ (z i) 0 := (contDiffAt_id.pow _).mul (hv i)
    exact ⟨ContDiffAt.sum (f:=z) (fun i _=>he i), (ink_list I z (fun i _=> he i) u).trans (sum_congr rfl fun i _=> by unfold z m; rw [ink_t_pow (f:=fun t=> F i (t*x)) (hv i),pulse_c (hf i)])⟩
  have hl : (fun x=>∑ i∈I,m F i x)=(fun x=>∑ i∈I,m H i x) := by funext x; rw [← (hx _ h x).2, ← (hx _ hp x).2]; exact aspiredV (he x) (ink_aspire (hx _ h x).1) (ink_aspire (hx _ hp x).1) hj
  have hr (p : ℕ→ℝ→ℝ) : ink (fun x=> ∑ i∈I,m p i x) j= ink (p q) j := by
    have hu : u-q=j:=by unfold u; omega
    rw [ink_list I (m p) (fun i _=> by unfold m; split_ifs; exact (contDiffAt_id.pow _).mul contDiffAt_const; exact contDiffAt_const),sum_eq_single_of_mem q hq]
    · unfold m; simp only [show q ≤ u by unfold u; omega, if_true,hu,ink_single]
    intro i hi he; unfold m; split; next hy=> rw [ink_single,if_neg]; omega
    next H=> exact congr_fun ink_z _
  rw [← hr F,← hr H,hl]
lemma shore_ray (i : Site m) (τ : ℕ) (h:Shore i τ U) (p n)(hn : τ≤n+p) (u v : ℝ→Link G m) (hu : AnalyticAt ℝ u 0) (hv : AnalyticAt ℝ v 0) (he : GaugeNear (suitify u) (suitify v)) :
    Fit (n+1) (large i n (strand τ p U)∘suitify u) (large i n (strand τ p U)∘suitify v) := by
  let L:=n+p-τ
  let S w q:= large i (L+τ-q) (strand τ q U)∘suitify w
  have hT : L+τ-p=n := by unfold L; omega
  have hx x (w : ℝ→ Link G m) (h : AnalyticAt ℝ w 0) : AnalyticAt ℝ (fun t:ℝ=> x • w (t*x)) 0 := (analyticAt_const (v:=x)).smul  (AnalyticAt.comp (f:=fun t=>t*x) ((zero_mul (x:ℝ)).symm ▸ h) (analyticAt_id.mul analyticAt_const))
  have hy x (w : ℝ→Link G m) : suitify (fun t:ℝ=> x • w (t*x))=(fun t:ℝ=> suitify w (t*x)) := funext fun t=>smul_smul t (x:ℝ) _
  have hh (x:ℝ) : Fit (L+τ+1) (fun t=>∑ q∈Finset.range (L+τ+1), t^q*S u q (t*x)) (fun t=>∑ q∈Finset.range (L+τ+1), t^q*S v q (t*x)) := by
    have hU := hx x u hu; have hV:= hx x v hv
    have hg : GaugeNear (suitify (fun t:ℝ=> x • u (t*x))) (suitify (fun t:ℝ=>x • v (t*x))) := by rw [hy,hy]; exact gauge_comp he _ (by simpa using! (((continuous_id (X:=ℝ)).mul_const x).tendsto 0))
    have hp (w:ℝ→Link G m) (t : ℝ) : (∑ q∈Finset.range (L+τ+1),t^q*S w q (t*x))= t^τ*arco m (fun e=>large i (τ+e) (U e)) (fun t=> x • w (t*x)) L t := by simp only [S, Function.comp_apply]; rw [← congr_fun (hy x w) t]; exact resume ..
    simp_rw [hp]; rw [show L+τ+1=τ+(L+1) by omega]; exact (h _ _ hU hV hg L).right (ruler τ τ le_rfl)
  have H w (h : AnalyticAt ℝ w 0) p : ContDiffAt ℝ ∞ (S w p) 0 := (large_smooth i _).contDiffAt.of_le le_top|>.comp _ ((contDiffAt_id.smul h.contDiffAt).of_le le_top)
  have hg : Fit (n+1) (S u p) (S v p) := pulse_bound (fun b hb=> grade_mark (H u hu) (H v hv) hh p (by simp; unfold L; omega) b (by simp only [Finset.mem_range] at hb; omega)) (H _ hu _) (H _ hv _)
  simpa only [S,hT] using hg
lemma shore_line (i : Site m) (h:Shore i τ U) (p n) (hn : τ ≤ n+p) (u v : ℝ→Link G m)(hU : AnalyticAt ℝ u 0)(hu:u 0=0)(hV:AnalyticAt ℝ v 0)(hv:v 0=0)(he:GaugeNear u v) :
    Fit (n+1) (large i n (strand τ p U)∘u) (large i n (strand τ p U)∘v) := by
  obtain ⟨a,ha,hh⟩:=stretchable hU hu; obtain ⟨b,hb,hB⟩:=stretchable hV hv; obtain ⟨X,k,hX,hY⟩:= he
  have ht : GaugeNear (suitify a) (suitify b) := ⟨X,k,hX,by filter_upwards [hh,hB,hY] with x hh hB hY; rw [hh,hB] at hY; exact hY⟩
  let F:=large i n (strand τ p U)
  exact (Fit.supply ((hh.filter_mono nhdsWithin_le_nhds).mono fun x hx=> congr_arg F hx) (n+1)).join ((shore_ray i τ h p n hn a b ha hb ht).join (Fit.supply ((hB.filter_mono nhdsWithin_le_nhds).mono fun x hx=> congr_arg F hx.symm) _))
end YM.RG08.Loom
