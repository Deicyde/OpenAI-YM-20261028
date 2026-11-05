import YM.EveryPhase.Strip

/-!
# Joint limits with exterior complex-time heights at interior

Keep the tied partial shore tracked by the actual exchange panes. The anchors
for the arguments are *global* positions, using a relative REAL t for the
stress slot. Do not assert convergence of the unintegrated stress across the
tied boundary on nonspacelike arguments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter MeasureTheory Metric Boundary Next.BOUNDARY Mink Complex Probe
open Work.C20
open scoped Topology BigOperators
variable {n : ℕ}

-- compactness with constants absorbed by filter atTop
lemma safeguard {A B : Type*} [TopologicalSpace B] {L : Filter A} {f : A × B → ℝ} {t : Set B}
    (h : IsCompact t) (he : ∀ y∈t, ∃ M : ℝ, ∀ᶠ x in L ×ˢ 𝓝 y, f x ≤ M) :
    ∃ M : ℝ, ∀ᶠ x in L, ∀ y∈t, f (x,y) ≤ M := by
  have hh : {z : (ℝ × A) × B | f (z.1.2,z.2) ≤ z.1.1} ∈ (atTop ×ˢ L) ×ˢ (𝓝ˢ t) := by
    apply h.mem_prod_nhdsSet_of_forall
    intro b hb
    obtain ⟨M,hM⟩ := he b hb
    have ht : Tendsto (fun z : (ℝ × A) × B => (z.1.2,z.2)) ((atTop ×ˢ L) ×ˢ 𝓝 b) (L ×ˢ 𝓝 b) :=
      (tendsto_snd.comp tendsto_fst).prodMk tendsto_snd
    filter_upwards [ht.eventually hM,(tendsto_fst.comp tendsto_fst).eventually (eventually_ge_atTop M)] with i hi hI
    exact le_trans hi hI
  obtain ⟨M,hM,T,hT,h⟩ := mem_prod_iff.mp hh
  obtain ⟨C,hC,U,hU,u⟩ := mem_prod_iff.mp hM
  obtain ⟨p,hp⟩ := Filter.nonempty_of_mem hC
  refine ⟨p,?_⟩; filter_upwards [hU] with x hx k hk
  exact h (show ((p,x),k)∈M ×ˢ T from ⟨u ⟨hp,hx⟩, subset_of_mem_nhdsSet hT hk⟩)

abbrev Dock (n : ℕ) := (SpacePoints n × Times n) × ℝ

def town (p : Dock n) (k : Fin n) := p.1.2 k + (p.2:ℂ)
def morn (p : Dock n) (k : Fin n) (s : ℝ) := town p k + s*I
def eve (p : Dock n) (k : Fin n) (s : ℝ) := town p k - s*I

lemma affordable (p : Dock n) (h : p.1.2∈strict n) (k : Fin n) : ∀ᶠ w in (𝓝 p) ×ˢ (𝓝[>] (0:ℝ)),
    hole k.succ w.1.1.2 (morn w.1 k w.2) ∈ strict (n+1) ∧ hole k.castSucc w.1.1.2 (eve w.1 k w.2)∈strict (n+1) := by
  obtain ⟨d,hd,hh⟩ := affords h k
  have hu : Continuous (fun p : Dock n => p.1.2) := by fun_prop
  filter_upwards [(tendsto_fst).eventually ((hu.tendsto p).eventually hh),
    (tendsto_snd).eventually (show ∀ᶠ s : ℝ in 𝓝[>] 0, 0<s from self_mem_nhdsWithin),
    (tendsto_snd.mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds hd)] with w hw hs ht
  exact hw.2 _ _ (by simp [town]) hs ht

def sundial (p : Dock n) (k : Fin n) : Heights (n+1) := hole k.succ (fun i => (p.1.2 i).im) ((p.1.2 k).im)
def scene (p : Dock n) (r : Space3) (k : Fin n) :=
    seat k.succ (place p.1.1 (fun i => (p.1.2 i).re)) (position r (town p k).re)
lemma arrival (p : Dock n) (r : Space3) (k : Fin n) :
    lodge k.succ p.1.1 p.1.2 r (town p k)=glow (scene p r k) (dawn (sundial p k)) := by
  unfold lodge laid; congr 1
  · ext1 i; refine Fin.succAboveCases k.succ ?_ ?_ i <;> simp [place,scene]
  congr 1; funext j; refine Fin.succAboveCases k.succ ?_ ?_ j <;> simp [sundial,town]
lemma apparition (p : Dock n) (r : Space3) (k : Fin n) :
    scene p r k∈(pair k).gap ↔ |p.2| < ‖r-p.1.1 k‖ := by
  rw [NearPair.gap,Set.mem_setOf]
  change seat _ _ _ k.succ - scene p r k k.castSucc ∈ Mink.spacelike ↔ _
  rw [lateral,seat_seat,
    show scene p r k k.castSucc = position (p.1.1 k) (p.1.2 k).re from calc
      _ = scene p r k (k.succ.succAbove k) := by rw [first_slot]
      _ = _ := by rw [scene,seat_next]; rfl]
  simp [sub_eq_add_neg,town]

variable {G : Gauge} {L : Register G} {S : Table L} {W : Surface S}
  {D : ∀ n, Blanket n} {Z : W.Aurora D} {P : DiffPlan S} {H : S.RealSpin} {F : Waves S}

def atlases (Z : W.Aurora D) (y : Heights (n+1)) (k : Fin n) := ∀ v : Fin (n+1) → S.Union,
    ∃ B : (pair k).Panes Z v y, B.sameGround

lemma displacement {t : Type*} {L' : Filter t} {x : t → Dock n} {u : t → Space3} {s : t → ℝ}
    {p : Dock n} {r : Space3} (k : Fin n) (hp : p.1.2∈strict n)
    (hx : Tendsto x L' (𝓝 p)) (hu : Tendsto u L' (𝓝 r)) (hs : Tendsto s L' (𝓝[>] 0)) :
    Tendsto (fun w => lodge k.succ (x w).1.1 (x w).1.2 (u w) (morn (x w) k (s w))) L'
      (𝓝[tube (n+1)] (glow (scene p r k) (dawn (sundial p k)))) ∧
    Tendsto (fun w => lodge k.succ (x w).1.1 (x w).1.2 (u w) (eve (x w) k (s w))) L'
      (𝓝[(pair k).name ⁻¹' tube (n+1)] (glow (scene p r k) (dawn (sundial p k)))) := by
  have hw := hx.prodMk hs
  have he : Tendsto (fun w => (x w,s w)) L' (𝓝 (p,0)) := hx.prodMk_nhds (hs.mono_right nhdsWithin_le_nhds)
  have hm : Continuous (fun i : Dock n × ℝ => morn i.1 k i.2) := by unfold morn town; fun_prop
  have hv : Continuous (fun i : Dock n × ℝ => eve i.1 k i.2) := by unfold eve town; fun_prop
  have hM := (hm.tendsto (p,0)).comp he
  have hV := (hv.tendsto (p,0)).comp he
  rw [← arrival]
  have ht (f : t → ℂ) (hh : Tendsto f L' (𝓝 (town p k))) : Tendsto
      (fun w => lodge k.succ (x w).1.1 (x w).1.2 (u w) (f w)) L' (𝓝 (lodge k.succ p.1.1 p.1.2 r (town p k))) := by
    change Tendsto ((fun p : (SpacePoints n × Times n) × (Space3 × ℂ) => lodge k.succ p.1.1 p.1.2 p.2.1 p.2.2) ∘
      (fun w => ((x w).1,(u w,f w)))) L' (𝓝 _)
    exact (lodge_cont k.succ).continuousAt.tendsto (x := (p.1,(r,town p k))) |>.comp (((continuous_fst.tendsto p).comp hx).prodMk_nhds (hu.prodMk_nhds hh))
  refine ⟨tendsto_nhdsWithin_iff.mpr ⟨ht _ ?_,?_⟩,tendsto_nhdsWithin_iff.mpr ⟨ht _ ?_,?_⟩⟩ -- order
  · simpa [morn] using! hM
  · exact (hw.eventually (affordable p hp k)).mono (fun i hi => laid_inside _ hi.1)
  · simpa [eve] using! hV
  filter_upwards [hw.eventually (affordable p hp k)] with i hi
  rw [mem_preimage,lodge_name]; exact laid_inside _ hi.2

lemma tidal_bend (K : Killing) (T : S.Stress) (v : Fin n → S.Union) (k : Fin n)
    (p : Dock n) (hp : p.1.2∈strict n) (he : atlases Z (sundial p k) k) (j : Axis)
    (r : Space3) (hr : |p.2|<‖r-p.1.1 k‖) :
    let L := ((𝓝 p) ×ˢ (𝓝[>] (0:ℝ))) ×ˢ 𝓝 r
    ∃ a : ℂ,
      Tendsto (fun w : (Dock n × ℝ) × Space3 => waveT Z K v T k.succ j w.1.1.1.1 w.1.1.1.2 (morn w.1.1 k w.1.2) w.2) L (𝓝 a) ∧
      Tendsto (fun w : (Dock n × ℝ) × Space3 => waveT Z K v T k.castSucc j w.1.1.1.1 w.1.1.1.2 (eve w.1.1 k w.1.2) w.2) L (𝓝 a) := by
  intro L
  let P := pair k
  choose Y hY using he
  have h : scene p r k∈P.gap := (apparition ..).2 hr
  let t := glow (scene p r k) (dawn (sundial p k))
  have ht : lodge k.succ p.1.1 p.1.2 r (town p k)=t := arrival ..
  let Z₁ (w : (Dock n × ℝ) × Space3) := lodge k.succ w.1.1.1.1 w.1.1.1.2 w.2 (morn w.1.1 k w.1.2)
  let Z₂ (w : (Dock n × ℝ) × Space3) := lodge k.succ w.1.1.1.1 w.1.1.1.2 w.2 (eve w.1.1 k w.1.2)
  have ht : Tendsto Z₁ L (𝓝[tube (n+1)] t) ∧ Tendsto Z₂ L (𝓝[P.name ⁻¹' tube (n+1)] t) :=
    displacement k hp (x:=fun w : (Dock n × ℝ) × Space3 => w.1.1) (u:=Prod.snd) (s:=fun w => w.1.2)
      (tendsto_fst.comp tendsto_fst) tendsto_snd (tendsto_snd.comp tendsto_fst)
  let l (a : Axis) := hole k.succ v (S.pin 4 (T j a))
  let M a := Y (l a)
  let H a := (M a).original _ h
  let J a := (M a).tilted _ h
  let b (a : Axis) := K.w a (fun i => t (k.succ,i))* (H a).extendF t
  refine ⟨∑ i : Axis, b i, ?_,?_⟩ <;> unfold waveT tide <;> refine tendsto_finsetSum _ fun a _ => ?_
  · have hm : Tendsto (fun w => Z.emit (l a) (Z₁ w)) L (𝓝 ((H a).extendF t)) :=
      ((H a).doc.continuousAt.tendsto.comp (ht.1.mono_right nhdsWithin_le_nhds)).congr' (ht.1.eventually (H a).fits)
    exact (((K.momentum a k.succ t).continuousAt.tendsto).comp (ht.1.mono_right nhdsWithin_le_nhds)).mul hm
  have hh : (H a).extendF =ᶠ[𝓝 t] (J a).extendF := (M a).reaches (hY (l a)) _ _
  have hv : Tendsto (fun w => Z.emit (l a ∘ P.s) (P.name (Z₂ w))) L (𝓝 ((H a).extendF t)) :=
    ((H a).doc.continuousAt.tendsto.comp (ht.2.mono_right nhdsWithin_le_nhds)).congr'
      (by filter_upwards [(ht.2.mono_right nhdsWithin_le_nhds).eventually hh, ht.2.eventually (J a).fits] with x hx hy
          exact hx.trans hy)
  refine ((((K.momentum a k.succ t).continuousAt.tendsto).comp (ht.2.mono_right nhdsWithin_le_nhds)).mul hv).congr' ?_
  filter_upwards with w
  change K.w a _ * Z.emit (l a ∘ P.s) (P.name (Z₂ w))=_
  rw [show (l a ∘ P.s) = _ from switch_hole k v (S.pin 4 (T j a)), show P.name (Z₂ w)= _ from lodge_name k _ _ _ _]
  simp only [Z₂,lodge,laid_at,hole_self]

lemma tidal_limit (K : Killing) (T : S.Stress) (v : Fin n → S.Union) (k : Fin n)
    (p : Dock n) (hp : p.1.2∈strict n) (he : atlases Z (sundial p k) k) (hZ : Z.FullBody F)
    (i : SpaceAxis) (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hr : ∀ r∈tsupport (drift g i), |p.2|<‖r-p.1.1 k‖) :
    ∃ a : ℂ,
      Tendsto (fun w : Dock n × ℝ => ∫ r, drift g i r * waveT Z K v T k.succ i.castSucc w.1.1.1 w.1.1.2 (morn w.1 k w.2) r)
        (𝓝 p ×ˢ 𝓝[>] 0) (𝓝 a) ∧
      Tendsto (fun w : Dock n × ℝ => ∫ r, drift g i r * waveT Z K v T k.castSucc i.castSucc w.1.1.1 w.1.1.2 (eve w.1 k w.2) r)
        (𝓝 p ×ˢ 𝓝[>] 0) (𝓝 a) := by
  let L := 𝓝 p ×ˢ 𝓝[>] (0:ℝ)
  let d := drift g i
  let s := tsupport d
  have hc : IsCompact s := drift_compact g hg i
  classical
  choose f hf hF using (show ∀ r : Space3, ∃ a : ℂ, (r∈s → Tendsto
    (fun w : (Dock n × ℝ) × Space3 => waveT Z K v T k.succ i.castSucc w.1.1.1.1 w.1.1.1.2 (morn w.1.1 k w.1.2) w.2) (L ×ˢ 𝓝 r) (𝓝 a)) ∧ (r∈s → Tendsto
    (fun w : (Dock n × ℝ) × Space3 => waveT Z K v T k.castSucc i.castSucc w.1.1.1.1 w.1.1.1.2 (eve w.1.1 k w.1.2) w.2) (L ×ˢ 𝓝 r) (𝓝 a)) from by
    intro r
    by_cases h : r∈s
    · obtain ⟨a,hp,hh⟩ := tidal_bend K T v k p hp he i.castSucc r (hr r h); exact ⟨a,fun _ => hp, fun _ => hh⟩
    exact ⟨0,fun hh => (h hh).elim, fun hh => (h hh).elim⟩)
  have hm (b : Dock n × ℝ → Space3 → ℂ) (hv : ∀ r∈s,
      Tendsto (fun w : (Dock n × ℝ) × Space3 => b w.1 w.2) (L ×ˢ 𝓝 r) (𝓝 (f r)))
      (hh : ∀ᶠ w in L, Continuous (b w)) : Tendsto (fun w => ∫ r, d r*b w r) L (𝓝 (∫ r, d r*f r)) := by
    have hi (r) (hr : r∈s) : Tendsto (fun w : (Dock n × ℝ) × Space3 => d w.2*b w.1 w.2) (L ×ˢ 𝓝 r)
        (𝓝 (d r*f r)) := ((d.continuous.tendsto r).comp tendsto_snd).mul (hv r hr)
    obtain ⟨M,hM⟩ := safeguard (L:=L) (f:=fun p : (Dock n × ℝ) × Space3 => ‖d p.2*b p.1 p.2‖) hc (fun y hy =>
      ⟨‖d y*f y‖+1,(hi y hy).norm.eventually (ge_mem_nhds (by simp))⟩)
    refine tendsto_integral_filter_of_dominated_convergence (F:=fun w r => d r*b w r) (s.indicator fun _ => M)
      (hh.mono fun w hw => (d.continuous.mul hw).aestronglyMeasurable) ?_
      ((integrable_indicator_iff hc.measurableSet).mpr (integrableOn_const hc.measure_ne_top)) ?_
    · filter_upwards [hM] with w hw; filter_upwards with x
      by_cases h : x∈s
      · rw [Set.indicator_of_mem h]; exact hw x h
      simp [h,image_eq_zero_of_notMem_tsupport h]
    filter_upwards with x
    by_cases h : x∈s
    · have he : Tendsto (fun w : Dock n × ℝ => (w,x)) L (L ×ˢ 𝓝 x) := tendsto_id.prodMk (tendsto_const_nhds (x:=x))
      change Tendsto ((fun w : (Dock n × ℝ) × Space3 => d w.2*b w.1 w.2) ∘ fun w => (w,x)) L (𝓝 _)
      exact (hi x h).comp he
    simp only [image_eq_zero_of_notMem_tsupport h, zero_mul]; exact tendsto_const_nhds
  have hy := affordable p hp k
  refine ⟨(∫ r, d r*f r), hm _ hf (hy.mono ?_), hm _ hF (hy.mono ?_)⟩
  · intro i hi; exact (waveT_smooth K v T _ _ _ _ hi.1 _ hZ).continuous
  intro i hi; exact (waveT_smooth K v T _ _ _ _ hi.2 _ hZ).continuous

def allows (p : Dock n) (g : Probe Space3) (k : Fin n) := ∀ i, ∀ r∈tsupport (drift g i), |p.2|<‖r-p.1.1 k‖

lemma tidal_shift (K : Killing) (T : S.Stress) (v : Fin n → S.Union) (k : Fin n)
    (p : Dock n) (hp : p.1.2∈strict n) (he : atlases Z (sundial p k) k) (hZ : Z.FullBody F)
    (g : Probe Space3) (hg : HasCompactSupport ⇑g) (hr : allows p g k) :
    ∃ a : ℂ,
      Tendsto (fun w : Dock n × ℝ => docks Z K v T g k.succ w.1.1.1 w.1.1.2 (morn w.1 k w.2))
        (𝓝 p ×ˢ 𝓝[>] 0) (𝓝 a) ∧
      Tendsto (fun w : Dock n × ℝ => docks Z K v T g k.castSucc w.1.1.1 w.1.1.2 (eve w.1 k w.2))
        (𝓝 p ×ˢ 𝓝[>] 0) (𝓝 a) := by
  choose a ha hA using (fun i => tidal_limit K T v k p hp he hZ i g hg (hr i))
  exact ⟨∑ i,a i, tendsto_finsetSum _ (fun i _ => ha i), tendsto_finsetSum _ (fun i _ => hA i)⟩
end YM.EveryPhase.Stress
