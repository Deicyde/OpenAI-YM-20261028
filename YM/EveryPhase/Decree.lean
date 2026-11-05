import YM.EveryPhase.Frost
/-!
# Partial and joint real distribution limits

Simple polynomial weights, any absolute spectator coordinates, compact
support of the field and spectator tests here. `Jury` specifies testable
relative ranges. No contact limits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter MeasureTheory Metric Boundary Next.BOUNDARY Mink Complex Probe Table
open Next.BOUNDARY.Descent
open scoped Topology BigOperators
variable {G : Gauge} {L : Register G} {S U : Table L} {W : Surface S}
  {D : ∀ n, Blanket n} {Z : W.Aurora D} {P : DiffPlan S} {F : Waves S} {H : S.RealSpin} {n : ℕ}

lemma cloth_split (j : Fin (n+1)) (M : Joint n) (K : Killing) (b : Axis) (s : ℝ) (g) :
    cloth M j (stack K b s g) = zeta b • cloth M j (touch K b g) + affect K b s • cloth M j g := by
  ext1 x; obtain ⟨⟨x,y⟩,rfl⟩ := (chairs j).surjective x
  change cloth _ _ _ (seat j x y)=(zeta b • cloth M j (touch K b g)+affect K b s • cloth M j g) (seat j x y)
  simp only [clothes,stack,_root_.add_apply,_root_.smul_apply,smul_eq_mul]; ring

lemma variations {A : Type*} {L : Filter A} (W : Surface S) (D : ∀ n, Blanket n) (K : Killing) (T : S.Stress)
    (v : Fin n → S.Union) (j : Fin (n+1)) (M : Joint n) (g : Probe Space3) (f : Probe ℝ) (hD : (D (n+1)).Modified)
    {s : ℝ} {p : Heights n} (hp : dawn (hole j p s)∈shores (n+1)) {i : A → Heights n} {a : A → ℝ}
    (hi : Tendsto (fun x => dawn (hole j (i x) (a x))) L (𝓝[shores (n+1)] (dawn (hole j p s))))
    (ha : Tendsto a L (𝓝 s)) : Tendsto (fun x => gavel W D K T v j M g f (i x) (a x)) L
      (𝓝 (gavel W D K T v j M g f p s)) := by
  have ht b (q : Joint (n+1)) := ((D _).tends hD (W.W (n+1) (hole j v (S.pin 4 (T timeAxis b)))) q _ hp).tendsto.comp hi
  unfold gavel; refine tendsto_finsetSum _ fun b _ => ?_
  simp_rw [cloth_split,map_add,map_smul,smul_eq_mul]
  exact ((ht b _).const_mul (zeta b)).add ((((affect_cont K b).tendsto s).comp ha).mul (ht b _))

lemma responses {A : Type*} {L : Filter A} (W : Surface S) (D : ∀ n, Blanket n) (K : Killing) (R : S.Rotation) (P : DiffPlan S)
    (v : Fin n → S.Tag) (k : Fin (n+1)) (t : S.Tag) (M : Joint (n+1)) (hD : (D (n+1)).Modified)
    {p : Heights (n+1)} (hp : dawn p∈shores (n+1)) {i : A → Heights (n+1)}
    (hi : Tendsto (fun x => dawn (i x)) L (𝓝[shores (n+1)] (dawn p))) :
    Tendsto (fun x => mandate W D K R P v k t M (i x)) L (𝓝 (mandate W D K R P v k t M p)) := by
  have ht (b : S.Tag) (q : Joint (n+1)) :=
    ((D _).tends hD (W.W _ (Bid.ink (hole k v b))) q _ hp).tendsto.comp hi
  have ha : Tendsto (fun x => i x k) L (𝓝 (p k)) := by
    have hh : Continuous (fun v : Points (n+1) => YM.time (v k)) := by fun_prop
    simpa [dawn, place,comp_def] using ((hh.tendsto (dawn p)).comp (hi.mono_right nhdsWithin_le_nhds))
  unfold mandate; simp only [loads,map_add,map_smul,smul_eq_mul]
  refine (ht ⟨_,rankAction R t.1 K.V t.2⟩ M).add ?_
  refine tendsto_finsetSum _ fun b _ => ?_
  let a : S.Tag := ⟨t.1+1,P.deriv t.1 b t.2⟩
  exact ((ht a _).const_mul (zeta b)).add ((((affect_cont K b).tendsto _).comp ha).mul (ht a M))

lemma grades (k : Fin n) (y : Heights n) (h : y∈east n) : ∀ᶠ s : ℝ in 𝓝[>] 0,
    hole k.succ y (y k+s)∈east (n+1) ∧ hole k.castSucc y (y k-s)∈east (n+1) := by
  let p := survey y 0 k 0
  have he := affordable p (shift_strict h 0) k
  have ht : Tendsto (fun s : ℝ => (p,s)) (𝓝[>] 0) (𝓝 p ×ˢ 𝓝[>] 0) := tendsto_const_nhds.prodMk tendsto_id
  have hh (j : Fin (n+1)) s (hx : hole j (shift 0 y) (arch 0 s) ∈ strict (n+1)) : hole j y s∈east (n+1) := by
    rw [← shift_scene 0 y j 0 s 0] at hx; intro i k hi; simpa only [shift,Complex.add_im,mul_I_im,ofReal_im,zero_add,ofReal_re] using hx hi
  filter_upwards [ht.eventually he] with i hi
  change hole k.succ (shift 0 y) (morn p k i) ∈ strict (n+1) ∧ hole k.castSucc (shift 0 y) (eve p k i)∈strict (n+1) at hi
  simp only [p,morn_survey,eve_survey] at hi; exact ⟨hh _ _ hi.1,hh _ _ hi.2⟩

lemma twin (k : Fin n) (y : Heights n) : hole k.succ y (y k) = hole k.castSucc y (y k) := by
  rw [← switch_hole]; funext i
  change hole _ _ _ i = hole _ _ _ (Equiv.swap k.castSucc k.succ i)
  have he : hole k.succ y (y k) k.castSucc=y k := by rw [← first_slot,hole_next]
  by_cases h : i=k.castSucc
  · rw [h,Equiv.swap_apply_left,he,hole_self]
  by_cases H : i=k.succ
  · rw [H,Equiv.swap_apply_right,hole_self,he]
  rw [Equiv.swap_apply_of_ne_of_ne h H]

-- In practice we only need local spacelike condition relative to B slot
structure Jury (g : Probe Space3) (f : Probe ℝ) (z : E4) : Prop where
  fits : g =ᶠ[𝓝 (spatial z)] fun _ => (1:ℂ)
  during (s : ℝ) (hs : s∈tsupport f) (i) (r) : r∈tsupport (drift g i) → |s-YM.time z|<‖r-spatial z‖

theorem partial_jump (K : Killing) (T : S.Stress) (v : Fin n → S.Tag) (k : Fin (n+1)) (B : S.Tag)
    (R : S.Rotation) (w : Prospect F Z U P H T) (h : StressLaws U T P.deriv R.lie) (M : Joint (n+1)) (hM : HasCompactSupport ⇑M)
    (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hr : ∀ r, ((g r).re:ℂ)=g r) (f : Probe ℝ) (hf : HasCompactSupport ⇑f)
    (y : Heights (n+1)) (hy : y∈east (n+1)) (he : (D (n+2)).Modified) (hA : atlases Z (hole k.succ y (y k)) k)
    (hk : ∀ x∈tsupport M, Jury g f (x k)) :
    let A := Bid.ink (hole k v B)
    gavel W D K T A k.succ M g f y (y k)-gavel W D K T A k.castSucc M g f y (y k)=
      mandate W D K R P v k B M y * ∫ x, f x := by
  intro A
  let L := 𝓝[>] (0:ℝ)
  have hh := grades k y hy
  let t := fun (i : Points (n+1) × ℝ) => survey y i.1 k i.2
  let u := crest Z K T A g k
  let l := trough Z K T A g k
  let X (s : ℝ) (i : Points (n+1) × ℝ) := M i.1*f i.2*u (t i,s)
  let Y (s : ℝ) (i : Points (n+1) × ℝ) := M i.1*f i.2*l (t i,s)
  let B₁ := fun i : Points (n+1) × ℝ => taskC Z K R P v k B (t i).1
  let B₂ := fun i : Points (n+1) × ℝ => M i.1*f i.2*B₁ i
  have h : ∀ᶠ s in L, Integrable (X s) ∧ Integrable (Y s) ∧
      gavel W D K T A k.succ M g f y (y k+s)= (∫ i, X s i) ∧ gavel W D K T A k.castSucc M g f y (y k-s)=∫ i, Y s i := by
    have ha p s : u (t p,s)= harbors Z K A T g k.succ (Boundary.trace p.1) (shift p.1 y) (arch p.2 (y k+s)) := by
      simp only [u,crest,t,morn_survey]; rfl
    have hc p s : l (t p,s)= harbors Z K A T g k.castSucc (Boundary.trace p.1) (shift p.1 y) (arch p.2 (y k-s)) := by
      simp only [l,trough,t,eve_survey]; rfl
    filter_upwards [hh] with a hk
    obtain ⟨h₁,h₂⟩ := harvest w.hZ K T A k.succ y M _ hk.1 g hg f hf hM
    obtain ⟨h₃,h₄⟩ := harvest w.hZ K T A k.castSucc y M _ hk.2 g hg f hf hM
    unfold X Y; simp_rw [ha,hc]; exact ⟨h₁,h₃,h₂,h₄⟩
  have hs : dawn (hole k.succ y (y k))∈shores (n+2) := by
    obtain ⟨b,_⟩ := hA (fun _ => 0); exact b.permitted.here
  have hp (j : Fin (n+2)) (q : ℝ → ℝ) (hq : Tendsto q L (𝓝 (y k))) (ht : ∀ᶠ s in L, hole j y (q s)∈east (n+2))
      (hw : dawn (hole j y (y k))∈shores (n+2)) : Tendsto (fun s => gavel W D K T A j M g f y (q s)) L
      (𝓝 (gavel W D K T A j M g f y (y k))) := by
    have hh : Continuous (fun r => dawn (hole j y r)) := by
      unfold dawn place hole position points; fun_prop
    refine variations W D K T A j M g f he (i:=fun _ => y) hw (tendsto_nhdsWithin_iff.mpr ?_) hq
    exact ⟨(hh.tendsto _).comp hq,ht.mono fun i hi => warmer _ (etched hi)⟩
  have h₁ : Tendsto (fun s : ℝ => y k+s) L (𝓝 (y k)) := by
    simpa only [add_zero,id_eq,L] using ((tendsto_const_nhds (x:=y k)).add (tendsto_id.mono_right (nhdsWithin_le_nhds (a:=0) (s:=Ioi 0))))
  have h₂ : Tendsto (fun s : ℝ => y k-s) L (𝓝 (y k)) := by
    simpa only [sub_zero,id_eq,L] using ((tendsto_const_nhds (x:=y k)).sub (tendsto_id.mono_right (nhdsWithin_le_nhds (a:=0) (s:=Ioi 0))))
  have ht := (hp k.succ _ h₁ (hh.mono fun i hi => hi.1) hs).sub
    (hp k.castSucc _ h₂ (hh.mono fun i hi => hi.2) ((twin k y) ▸ hs))
  let q := fun s p => X s p-Y s p
  let J := tsupport M ×ˢ tsupport f
  have hr p (hv : p∈J) : Tendsto (fun w : ℝ × (Points (n+1) × ℝ) => q w.1 w.2) (L ×ˢ 𝓝 p) (𝓝 (B₂ p)) := by
    have hm : Jury g f (p.1 k) := hk _ hv.1
    have ht := through_jump K T v k B R w ?_ g hg hr (t p) hm.fits (shift_strict hy p.1) (hm.during p.2 hv.2) (by
      dsimp only [t]; rw [dial]; exact hA)
    -- name shadow
    · have hy : Tendsto (fun i : ℝ × (Points (n+1) × ℝ) => (t i.2,i.1)) (L ×ˢ 𝓝 p) (𝓝 (t p) ×ˢ L) :=
        (((survey_walk y k).tendsto p).comp tendsto_snd).prodMk tendsto_fst
      have hc := (((M.continuous.comp continuous_fst).mul (f.continuous.comp continuous_snd)).tendsto p) |>.comp
        (tendsto_snd (f:=L))
      refine (hc.mul (ht.comp hy)).congr' ?_
      filter_upwards with i
      change M i.2.1*f i.2.2*(u (t i.2,i.1)-l (t i.2,i.1))=_; rw [mul_sub]
    assumption
  obtain ⟨c,hc⟩ := safeguard (f:=fun i : ℝ × (Points (n+1) × ℝ) => ‖q i.1 i.2‖) (L:=L) (hM.prod hf) (fun i hi =>
    ⟨‖B₂ i‖+1,(hr i hi).norm.eventually (ge_mem_nhds (by simp))⟩)
  have hb (p) (hv : p∉J) : M p.1*f p.2=0 := by
    by_cases hh : p.1∈tsupport M
    · rw [image_eq_zero_of_notMem_tsupport (show p.2∉tsupport f from fun h => hv ⟨hh,h⟩),mul_zero]
    simp [image_eq_zero_of_notMem_tsupport hh]
  classical
  have hq : Tendsto (fun s => ∫ p, q s p) L (𝓝 (∫ p, B₂ p)) := by
    refine tendsto_integral_filter_of_dominated_convergence (J.indicator fun _ => c)
      (h.mono fun i hi => (hi.1.sub hi.2.1).aestronglyMeasurable) ?_
      ((integrable_indicator_iff (hM.prod hf).measurableSet).2 (integrableOn_const (hM.prod hf).measure_ne_top)) ?_
    · filter_upwards [hc] with i hi; filter_upwards with p
      by_cases h : p∈J
      · rw [Set.indicator_of_mem h]; exact hi p h
      simp [q,X,Y,h,hb p h]
    filter_upwards with p
    by_cases h : p∈J
    · have hp : Tendsto (fun i => (i,p)) L (L ×ˢ 𝓝 p) := tendsto_id.prodMk tendsto_const_nhds
      change Tendsto ((fun w : ℝ × (Points (n+1) × ℝ) => q w.1 w.2) ∘ (fun s => (s,p))) L _
      exact (hr p h).comp hp
    simp only [q,X,Y,B₂,hb p h,zero_mul,sub_self]; exact tendsto_const_nhds
  have hv := tendsto_nhds_unique_of_eventuallyEq ht hq (by
    filter_upwards [h] with s hs
    unfold q; rw [integral_sub hs.1 hs.2.1,← hs.2.2.1,← hs.2.2.2])
  refine hv.trans ?_
  rw [(mandate_int w.hZ K R P v k B M y hy).2]
  change (∫ p, B₂ p ∂(volume.prod volume))=_
  rw [show B₂=fun p => (taskC Z K R P v k B (Boundary.trace p.1,shift p.1 y)*M p.1)*f p.2 by
    funext p; change M p.1*f p.2*taskC Z K R P v k B (Boundary.trace p.1,shift p.1 y)=_; ring]
  exact integral_prod_mul (fun p : Points (n+1) => taskC Z K R P v k B (Boundary.trace p,shift p y)*M p) (⇑f)

-- existence goes through all labels over the actual performance at common heights
structure Gallery (W : Surface S) (Z : W.Aurora D) : Prop where
  book : ∀ n, (D n).Modified
  spectra : Bid.cones W
  cases (n : ℕ) (k : Fin n) : ∃ t : ℕ → Heights (n+1), Tendsto (dawn ∘ t) atTop (𝓝 0) ∧
    ∀ i, atlases Z (t i) k

lemma ancestor (k : Fin n) (h : Gallery W Z) : ∃ y : ℕ → Heights n, Tendsto (fun t => dawn (y t)) atTop (𝓝 0) ∧
    (∀ i, y i∈east n) ∧ ∀ i, atlases Z (hole k.succ (y i) (y i k)) k := by
  obtain ⟨t,ht,h⟩ := h.cases n k
  let y (i : ℕ) : Heights n := t i ∘ k.succ.succAbove
  have hp (m : ℕ) : (pair k).spectator (t m) := by
    obtain ⟨B,hB⟩ := h m (fun _ => 0); exact B.permitted.willing
  have hh : Tendsto y atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr; intro j
    have he : Continuous (fun p : Points (n+1) => YM.time (p (k.succ.succAbove j))) := by fun_prop
    simpa [y,dawn,comp_def,place] using ((he.tendsto 0).comp ht)
  refine ⟨y,?_,?_,?_⟩
  · have ht : Continuous (@dawn n) := by unfold dawn place points position; fun_prop
    rw [show (0 : Points n)=dawn 0 by ext1 i; apply ext_by <;> simp [dawn,place]]
    exact (ht.tendsto 0).comp hh
  · intro i x z hx
    exact (hp i).2 _ _ ((Fin.strictMono_succAbove _) hx)
      (Or.inr (Fin.succAbove_ne k.succ z))
  intro i
  rw [show hole k.succ (y i) (y i k) = t i by
    funext l; refine Fin.succAboveCases k.succ ?_ ?_ l
    · rw [hole_self]; unfold y; rw [Function.comp_apply,first_slot]; exact (hp i).1
    intro z; rw [hole_next]; rfl]; exact h i

def stamp (W : Surface S) (K : Killing) (T : S.Stress) (v : Fin n → S.Union) (j : Fin (n+1))
    (M : Joint n) (g : Probe Space3) (f : Probe ℝ) := ∑ b : Axis, zeta b* W.W (n+1)
      (hole j v (S.pin 4 (T timeAxis b))) (cloth M j (touch K b (pincushion g f)))

def receives (W : Surface S) (K : Killing) (R : S.Rotation) (P : DiffPlan S) (v : Fin n → S.Tag) (k : Fin (n+1))
    (t : S.Tag) (M : Joint (n+1)) :=
    let ψ := fun (a : S.Tag) => W.W (n+1) (Bid.ink (hole k v a))
    ψ ⟨t.1,rankAction R t.1 K.V t.2⟩ M+∑ b : Axis,
      zeta b * ψ ⟨t.1+1,P.deriv t.1 b t.2⟩ (effect K b (PiLp.proj 2 _ k) M)

lemma dawn_zero (n) : dawn (0:Heights n)=(0:Points n) := by ext1 i; apply ext_by <;> simp [dawn,place]

theorem verdict (K : Killing) (T : S.Stress) (v : Fin n → S.Tag) (k : Fin (n+1)) (B : S.Tag)
    (R : S.Rotation) (w : Prospect F Z U P H T) (h : StressLaws U T P.deriv R.lie) (M : Joint (n+1)) (hM : HasCompactSupport ⇑M)
    (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hr : ∀ r, ((g r).re:ℂ)=g r) (f : Probe ℝ) (hf : HasCompactSupport ⇑f)
    (ha : Gallery W Z) (hk : ∀ x∈tsupport M, Jury g f (x k)) :
    let A := Bid.ink (hole k v B)
    stamp W K T A k.succ M g f-stamp W K T A k.castSucc M g f=receives W K R P v k B M * ∫ x, f x := by
  intro A
  obtain ⟨y,hy,hh,hA⟩ := ancestor k ha
  have hb (i) : dawn (hole k.succ (y i) (y i k))∈shores (n+2) := by
    obtain ⟨C,hC⟩ := hA i (fun _ => 0); exact C.permitted.here
  have hv := ha.spectra
  have he n v : (D n).partialD (W.W n v) 0=W.W n v := (D n).flatD (ha.book n) (hv n v)
  have hY : Tendsto y atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr; intro i
    have hh : Continuous (fun p : Points (n+1) => YM.time (p i)) := by fun_prop
    simpa [comp_def,dawn,place] using ((hh.tendsto 0).comp hy)
  have h₀ : Tendsto (fun i => mandate W D K R P v k B M (y i)) atTop (𝓝 (receives W K R P v k B M)) := by
    have hx : Tendsto (fun x => dawn (y x)) atTop (𝓝[shores (n+1)] 0) := tendsto_nhdsWithin_iff.mpr ⟨hy,
      Eventually.of_forall fun i => warmer _ (etched (hh i))⟩
    rw [← dawn_zero (n+1)] at hx
    have hu := responses W D K R P v k B M (ha.book _) (by rw [dawn_zero]; exact flat _) hx
    rw [show mandate W D K R P v k B M 0=receives W K R P v k B M by
      simp [mandate,loads,dawn_zero,affect,he,receives] ] at hu; exact hu
  have hu (j : Fin (n+2)) (hj : ∀ i, dawn (hole j (y i) (y i k)) ∈ shores (n+2)) : Tendsto
      (fun i => gavel W D K T A j M g f (y i) (y i k)) atTop (𝓝 (stamp W K T A j M g f)) := by
    have hc : Tendsto (fun i => y i k) atTop (𝓝 0) := (tendsto_pi_nhds.mp hY k)
    have hp : hole (A:=ℝ) j 0 0=0 := by funext i; refine Fin.succAboveCases j ?_ ?_ i <;> simp
    have he₁ : Continuous (fun p : Heights (n+1) × ℝ => dawn (hole j p.1 p.2)) := by unfold dawn hole place position points; fun_prop
    have ht := (variations W D K T A j M g f (ha.book _) (by rw [hp,dawn_zero]; exact flat _)
      (tendsto_nhdsWithin_iff.mpr ⟨(he₁.tendsto (0,0)).comp (hY.prodMk_nhds hc), Eventually.of_forall hj⟩) hc)
    rw [show gavel W D K T A j M g f 0 0=stamp W K T A j M g f by
      simp_rw [gavel,hp,dawn_zero,he, cloth_split, affect]; simp [stamp] ] at ht; exact ht
  exact tendsto_nhds_unique_of_eventuallyEq ((hu k.succ hb).sub (hu k.castSucc
    (fun i => (twin k (y i)) ▸ hb i))) (h₀.mul_const _) (Eventually.of_forall
      (fun i => partial_jump K T v k B R w h M hM g hg hr f hf (y i) (hh i) (ha.book _) (hA i) hk))
end YM.EveryPhase.Stress
