import YM.WilsonBulk.Heat.Bath

/-!
# Local overlap currency

Polchinski/web strict operations pay for values and pairwise cutoff
differences at the *kernel* norm. These do not assert `Atlas` on the whole
transition. Handles e.g. paying later ΔΓ (must be purchased at nonzero
mode-independent width) and A0-vs-tree charges. Want polynomial Schedule
price for newly chosen stage widths (not used for repeated contraction).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Sheet
open scoped Topology Classical ENNReal BigOperators
open Function Equiv Finset Filter Pert.Bulk
variable {X : Type} {σ θ η p q p' q' r' δ ε : ℝ} {G : Rule X} {e n k : ℕ}
variable {u u' v v' : Page X n}

/-- Same absolute width cap and cutoff difference δ times the cap. -/
structure Options (G : Rule X) (σ δ p : ℝ) (u v : Page X n) : Prop where
 nonneg : 0≤ δ
 plus : Within G σ p u
 minus : Within G σ p v
 variation : Within G σ (δ*p) (u-v)
namespace Options
variable (h : Options G σ δ p u v)
lemma baseline (h : Options G σ δ p u v) : 0 ≤ p := h.plus.1
include h
lemma more (he : δ ≤ ε) (hb : p ≤ q) (ha : θ ≤ σ) : Options G θ ε q u v :=
  ⟨h.nonneg.trans he,h.plus.mono ha hb,h.minus.mono ha hb,h.variation.mono ha (mul_le_mul he hb h.baseline (h.nonneg.trans he))⟩
lemma scale (c : ℝ) : Options G σ δ (|c| * p) (c • u) (c • v) :=
  ⟨h.nonneg,h.plus.scale c,h.minus.scale c,by rw [← smul_sub,mul_left_comm]; exact h.variation.scale _⟩
lemma neg : Options G σ δ p (-u) (-v) := by simpa using h.scale (-1)
lemma reindex (e : Fin n≃ Fin k) : Options G σ δ p (escort e u) (escort e v) :=
  ⟨h.nonneg,h.plus.reindex e,h.minus.reindex e,by rw [← escort_minus]; exact h.variation.reindex e⟩
lemma clean : Options G σ δ p (polish u) (polish v) := ⟨h.nonneg,h.plus.clean,h.minus.clean,by rw [← polish_minus]; exact h.variation.clean⟩
lemma add (hh : Options G σ δ q u' v') : Options G σ δ (p+q) (u+u') (v+v') := by
  refine ⟨h.nonneg,h.plus.add hh.plus,h.minus.add hh.minus,?_⟩
  rw [show u+u'-(v+v')=u-v+(u'-v') by abel,mul_add]; exact h.variation.add hh.variation
lemma sub (hh : Options G σ δ q u' v') : Options G σ δ (p+q) (u-u') (v-v') := by simpa only [sub_eq_add_neg] using h.add hh.neg
omit h
lemma self {u : Page X n} (hp : Within G σ p u) (he : 0≤δ) : Options G σ δ p u u := ⟨he,hp,hp,by rw [sub_self]; exact Within.zero (mul_nonneg he hp.1)⟩
lemma zero (hp : 0 ≤ p) (he : 0≤δ) : Options G σ δ p (0:Page X n) 0 := self (Within.zero hp) he
lemma gather {ι : Type} (s : Finset ι) {U V : ι → Page X n} {p : ι→ ℝ}
    (h : ∀ i∈s,Options G σ δ (p i) (U i) (V i)) (he : 0≤δ) : Options G σ δ (∑ i∈s,p i) (∑ i∈s,U i) (∑ i∈s,V i) := by
  induction s using Finset.induction with
  | empty => exact by simpa using (zero (n:=n) (G:=G) (σ:=σ) le_rfl he)
  | insert i s hh ih => simpa only [Finset.sum_insert hh] using (h i (mem_insert_self ..)).add (ih fun a ha=> h a (mem_insert_of_mem ha))
lemma plucked {u v : Page X (n+1)} (h : Options G σ δ p u v) (he : 0≤σ) (hp : n≠0) : Options G σ δ p (pluck u) (pluck v) :=
  ⟨h.nonneg,h.plus.plucked he,h.minus.plucked he,by rw [←pluck_sub h.plus h.minus he he hp]; exact h.variation.plucked he⟩
lemma double (h : Options G σ δ p u v) {u' v' : Page X k} (hh : Options G θ δ q u' v') : p*q ≤ 2*(p*q) := le_mul_of_one_le_left (mul_nonneg h.baseline hh.baseline) one_le_two
lemma overlaid {a a' : Page X k} (h : Options G σ δ p u v) (he : Options G θ δ q a a') (hp : 0≤θ) (hn : k≠0)
    (φ : Fin k → Fin n) : Options G σ δ (2*(p*q)) (overlay u a φ) (overlay v a' φ) := by
  refine ⟨h.nonneg,(h.plus.overlaid he.plus hp hn φ).mono le_rfl (h.double he), (h.minus.overlaid he.minus hp hn φ).mono le_rfl (h.double he),?_⟩
  rw [overlay_minus,show δ*(2*(p*q))=(δ*p)*q+p*(δ*q) by ring]; exact (h.variation.overlaid he.plus hp hn φ).add (h.minus.overlaid he.variation hp hn φ)
lemma sewn {u u' : Page X (k+1)} {v v' : Page X (n+1)} (h : Options G σ δ p u u') (hv : Options G σ δ q v v')
    (he : 0≤θ) (hs : ((n:ℝ)+1)*θ≤σ) (hp : ((k:ℝ)+1)*θ≤σ) : Options G θ δ (2*(p*q)) (seam u v) (seam u' v') := by
  refine ⟨h.nonneg,(h.plus.sewn hv.plus he hs hp).mono le_rfl (h.double hv), (h.minus.sewn hv.minus he hs hp).mono le_rfl (h.double hv),?_⟩
  rw [seam_tele,show δ*(2*(p*q))=(δ*p)*q+p*(δ*q) by ring]; exact (h.variation.sewn hv.plus he hs hp).add (h.minus.sewn hv.variation he hs hp)

lemma lap {u u':Page X (n+2)} {v v': Page X 2} (h : Options G θ δ q v v') (he : Options G σ δ p u u')
    (hp : 0 ≤ θ) (hs : 0 ≤ σ) (hn : n≠0) : Options G σ δ (dab n*(2*(p*q))) (lap v u) (lap v' u') := by
  have he := ((((he.overlaid h hp (by decide) (bond _)).plucked hs (by omega)).plucked hs hn).scale (dab n)).clean; rw [abs_of_pos (dab_pos _)] at he; exact he
end Options

-- common repeated width loss denominator K≥ e+3 at prescribed maximal degree; here using maximum valence, not charging schedule again for strict events
lemma cut_width {a b c : ℝ} (ha : 0≤a) (_hc : 0≤ c) (hb : c≤b) (hB : 0 < b) : c*(a/b) ≤ a := by
  rw [← mul_div_assoc,div_le_iff₀ hB]; rw [mul_comm c]; gcongr
lemma Options.grab {u u':Page X (k+1)} {v v': Page X 2} (h : Options G σ δ q u u') (he : Options G σ δ p v v')
    (hs : 0≤σ) (B : ℝ) (hb : 2≤ B) (hk : ((k:ℝ)+1)≤ B) : Options G (σ/B) δ (2*(q*p)) (grab v u) (grab v' u') := by
  have hB := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hb
  have ha : 0≤ σ/B := div_nonneg hs hB.le
  apply ((h.sewn he ha ?_ (cut_width hs (by positivity) hk hB)).plucked ha (by omega)).reindex (finRotate _)
  apply cut_width hs (by positivity) (by norm_num; exact hb) hB
lemma Options.bridge {u u' : Page X (k+1)} {v v' : Page X (n+1)} {A B : Page X 2} {w : ℝ}
    (hg : Options G σ δ p A B) (hu : Options G σ δ q u u') (hv : Options G σ δ r' v v')
    (hs : 0≤σ) (hb : 2≤ w) (hk : ((k:ℝ)+1)≤w) (ht : ((n:ℝ)+1)≤w) (hn : k+n≠0) :
    Options G ((σ/w)/w) δ (brush k n * (2*(2*(q*p)*r'))) (bridge A u v) (bridge B u' v') := by
  have hw: 0<w:= by linarith
  have hx := div_nonneg hs hw.le; have hy := div_nonneg hx hw.le
  have he := ((((hu.grab hg hs w hb hk).sewn (hv.more le_rfl le_rfl (div_le_self hs (by linarith))) hy (cut_width hx (by positivity) ht hw) (cut_width hx (by positivity) hk hw)).plucked hy hn).scale (brush k n)).clean
  rw [abs_of_pos (brush_pos ..)] at he; exact he
end Sheet
end YM.WilsonBulk
