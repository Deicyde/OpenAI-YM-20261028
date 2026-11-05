import YM.Push.RELAY_MARK.Rank

/-!
# Gauge invariant equation lifts

The Haar average stays within a *finite-dimensional span* on these
very sections at fixed D. Preserve even the nominal t-power
(that will supply Credit) and the avoidance cost (all spectators for the
actual cutoffs, no gauge hypothesis required on those spectators). .
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Filter MeasureTheory Wilson Lattice RG Source Source.Drops Labels Analysis Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ} {p q : Pol G} {f : Pre G} {m : ℕ × ℕ}

private lemma constant_gauge_cont (g : G.El) : Continuous (Lattice.gauge (R:=ℤ) (fun _ => g)) := by
  unfold Lattice.gauge; fun_prop

lemma change_above {p : Pol G} (h : p∈above m) (e : (i : ℕ) → Module.End ℝ (Taylor G i)) :
    changed e p∈above m := by
  classical
  unfold above at h; rw [MvPolynomial.restrictSupport_eq_span] at h
  induction h using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨x,hx,rfl⟩ := hp
    refine rise_later (b:=weight x) hx (rise_sector _ ?_)
    exact pure_moved (fun i => (i+2,1)) e x 1
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

lemma paint_parts (g : G.El) (h : Forms H d f p) : Forms H d (accord f g) (changed (fun _=>Taylor.paint g) p) := by
  have he (J : Jet G) (t : ℝ) : read (scaleJet J t) (changed (fun _=>Taylor.paint g) p)= read (scaleJet (colored g J) t) p := by
    rw [eval_changed,show changedJet (fun _=>Taylor.paint g) (scaleJet J t)=_ from ?_]
    funext i; simp [changedJet,scaleJet,colored]
  refine ⟨moved_limit h.bound _,fun J=> ?_,fun J k hk=>?_⟩
  · simp_rw [accord,comp_apply,← Work.G01.links_colored]
    exact h.nice _
  simp_rw [accord,comp_apply,← Work.G01.links_colored,he]; exact h.through _ _ hk

lemma micro_paint (g : G.El) (h : Micro f) : Micro (accord f g) := by
  obtain ⟨r,M,H⟩ := h.2
  refine ⟨h.1.comp (constant_gauge_cont _),r,M,fun n hn o β hb S hs hS=>?_⟩
  let k (U : Config G n) := Lattice.gauge (fun _=>g) U
  let l (U : Config G n) := Lattice.gauge (fun _=>g⁻¹) U
  let F := S ∘ l
  have he : LocalOn (Outer r o) F := by
    intro U V hh
    apply hs
    intro b hv hx
    unfold l Lattice.gauge; rw [hh b hv hx]
  have hl : Envelope F := ⟨hS.meas.comp (law_gauge β _).measurable,
    hS.cost.elim fun c hc => ⟨c,fun U=>hc _⟩⟩
  let Q := fun U => f (expandAt o U)*F U
  have hy : moment β Q = 0 := H n hn o β hb F he hl
  have hQ : Integrable Q (law G n β) := times_integrable (onStencil o h.1) hl
  have hm : moment β (Q ∘ k) = moment β Q := by
    have hM : MeasurePreserving k (law G n β) (law G n β) := law_gauge β _
    have ht := integral_map (μ:=law G n β) (φ:=k) (f:=Q) hM.aemeasurable (by rw [hM.map_eq]; exact hQ.aestronglyMeasurable)
    rw [hM.map_eq] at ht; exact ht.symm
  rw [← hy,← hm]; congr 1; funext U
  have hh : expandAt o (k U)=Lattice.gauge (fun _=>g) (expandAt o U) := expandAt_gauge ..
  have hb : l (k U)=U := by funext i; simp [l,k,Lattice.gauge]; group
  simp only [accord, comp_apply,Q,F,hh,hb]

lemma color_lift (g : G.El) (p : Label G d) (h : Cone H d m p.val f q) :
    Cone H d m p.val (accord f g) (changed (fun _=>Taylor.paint g) q) := by
  refine ⟨h.grows, paint_parts g h.maps, ?_, accord_power g h.size,micro_paint g h.mark⟩
  have he : changed (fun _=>Taylor.paint g) p.val=p.val := eval_ext _ _ (fun A=> (eval_changed ..).trans (p.property.2 A g))
  rw [← he,← map_sub]; exact change_above h.head _

lemma invariant_part (h : Forms H d f q) (hv : GaugeInvariant f) : q∈localFields G d := by
  refine ⟨h.bound,fun J u=>?_⟩
  have he := paint_parts u h
  rw [show accord f u = f from funext (fun U=> hv _ _)] at he
  change read (changedJet (fun _=>Taylor.paint u) J) q=read J q
  rw [← eval_changed,he.sole h]

section Finite

private lemma detection {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : G.El → V) {X : Type*} (B : X → (V →ₗ[ℂ] ℂ)) (h : ∀ x:V, (∀ i,B i x=0) → x=0)
    (hx : ∀ i, Continuous ((B i) ∘ f)) (Q : V →ₗ[ℂ] ℂ) : Continuous (Q ∘ f) := by
  let M := Submodule.span ℂ (range B)
  have he : Q∈M := by
    suffices hh : Q∈M.dualCoannihilator.dualAnnihilator by rwa [Subspace.dualCoannihilator_dualAnnihilator_eq] at hh
    apply (Submodule.mem_dualAnnihilator _).2; intro a ha
    rw [h _ (fun i => (Submodule.mem_dualCoannihilator _).1 ha _ (Submodule.subset_span (show B i∈range B from ⟨i,rfl⟩))),map_zero]
  induction he using Submodule.span_induction with
  | mem p hp=> obtain ⟨i,rfl⟩ := hp; exact hx i
  | zero=> exact continuous_const
  | add _ _ _ _ hf hg=> exact hf.add hg
  | smul z _ _ hg=> exact hg.const_smul z

private lemma average_exact {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : G.El→V) (h : ∀ B : V →ₗ[ℂ] ℂ, Continuous (B ∘ f)) :
    ∃ a : V, ∀ Q : V →ₗ[ℂ] ℂ,Q a=∫ g:G.El,Q (f g) ∂G.probHaar := by
  let B := Module.finBasis ℂ V
  let w i (g : G.El) := B.repr (f g) i
  refine ⟨∑ i,(∫ g, w i g ∂G.probHaar) • B i,fun Q=>?_⟩
  rw [map_sum]
  have he (g : G.El) : Q (f g)=∑ i, w i g * Q (B i) := by
    nth_rw 1 [← B.sum_repr (f g)]; rw [map_sum]; simp only [map_smul]; rfl
  simp_rw [he,map_smul]; rw [integral_finsetSum _ fun i _ => ?_]
  · exact Finset.sum_congr rfl fun i _=> (integral_mul_const ..).symm
  exact ((h (B.coord i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mul_const _

private lemma averaged (p : Label G d) (f : Pre G) (h : Cone H d m p.val f q) :
    ∃ t : Pol G, Cone H d m p.val (fun U => ∫ g:G.El, accord f g U ∂G.probHaar) t := by
  let F := fun g : G.El => ((1:ℂ),accord f g)
  let s := Submodule.span ℂ (range F)
  have he : s ≤ (⊤ : Submodule ℂ ℂ).prod (cluster f) := Submodule.span_le.mpr (fun t ⟨i,hi⟩ =>
      hi ▸ (show F i ∈ _ from ⟨Submodule.mem_top,Submodule.subset_span ⟨i,rfl⟩⟩))
  let V := (⊤ : Submodule ℂ ℂ).prod (cluster f)
  haveI : FiniteDimensional ℂ (cluster f) := cluster_finite h.size
  haveI : FiniteDimensional ℂ V := Module.Finite.of_fg (Submodule.FG.prod (Module.Finite.iff_fg.mp inferInstance) (Module.Finite.iff_fg.mp (cluster_finite h.size)))
  haveI : FiniteDimensional ℂ s := FiniteDimensional.of_injective (Submodule.inclusion he) (Submodule.inclusion_injective _)
  let x (g : G.El) : s := ⟨F g,Submodule.subset_span ⟨g,rfl⟩⟩
  let b : s →ₗ[ℂ] ℂ := (LinearMap.fst ℂ ℂ (Pre G)).comp s.subtype
  let c (U : CoverConfig G) : s →ₗ[ℂ] ℂ := (LinearMap.proj U).comp ((LinearMap.snd ℂ ℂ (Pre G)).comp s.subtype)
  have hb := detection x (X:=Option (CoverConfig G)) (fun i=> Option.elim i b c)
  have hX : ∀ T : s →ₗ[ℂ] ℂ, Continuous (T ∘ x) := by
    apply hb
    · intro y hy; apply Subtype.ext
      exact Prod.ext (hy none) (funext (fun U=>hy (some U)))
    rintro (_|U)
    · exact continuous_const
    change Continuous (fun g:G.El=> f (Lattice.gauge (fun _=>g) U))
    exact (power_cont h.size).comp (by unfold Lattice.gauge; fun_prop)
  obtain ⟨a,ha⟩ := average_exact x hX
  have hu (y : ℂ × Pre G) (hy : y∈s) : ∃ q, Cone H d m (y.1 • p.val) y.2 q := by
    induction hy using Submodule.span_induction with
    | mem z hz => obtain ⟨u,rfl⟩:=hz; exact ⟨_,by change Cone _ _ _ ((1:ℂ) • _) _ _; rw [one_smul]; exact color_lift u p h⟩
    | zero=> exact ⟨_,by rw [Prod.fst_zero,zero_smul,Prod.snd_zero]; exact Cone.zero ..⟩
    | add t u _ _ ha hb=> obtain ⟨z,hz⟩:=ha; obtain ⟨w,hw⟩:=hb; exact ⟨_,by rw [Prod.fst_add,Prod.snd_add,add_smul]; exact hz.add hw⟩
    | smul i u _ ha=> obtain ⟨z,hz⟩:=ha; exact ⟨_,by rw [Prod.smul_fst,Prod.smul_snd,smul_assoc]; exact hz.scale i⟩
  obtain ⟨z,hz⟩ := hu _ a.property
  have hh : a.val.1=1 := by
    change b a=1; rw [ha b]; change (∫ _:G.El,(1:ℂ) ∂G.probHaar)=1; simp
  have ht : a.val.2=fun U=>∫ g:G.El,accord f g U ∂G.probHaar := funext fun U=>ha (c U)
  rw [hh, ht,one_smul] at hz; exact ⟨z,hz⟩
end Finite

/-- Invariant version of `mounted_read` on actual labels. -/
theorem positioned (H : Hol G) (p : Label G d) (m : ℕ × ℕ) (h : m.1 ≤ d)
    (hp : p∈Grade m) (hv : p∈Maxwell.equationIdeal G d) :
    ∃ (f : Pre G) (q : Label G d), GaugeInvariant f ∧ Cone H d m p.val f q.val := by
  obtain ⟨f,w,hf⟩ := mounted_read H p m h hp hv
  let l : Pre G := fun U=>∫ g:G.El, accord f g U ∂G.probHaar
  -- With this l. Unconstrained Haar integral acts at the root, all other
  -- sites follow automatically for these transported factors.
  obtain ⟨t,ht⟩ := averaged p f hf
  have he : GaugeInvariant l := by
    intro u U; rw [gauge_root (f:=l) ht.size]
    let y := u 0
    have hu (g : G.El) : accord f g (Lattice.gauge (fun _=>y) U) = accord f (g*y) U := by
      unfold accord; rw [comp_apply,comp_apply,show Lattice.gauge (fun _=>g) (Lattice.gauge (fun _=>y) U) = Lattice.gauge (fun _=>g*y) U from funext (fun i=>by simp [Lattice.gauge,mul_assoc])]
    change (∫ g:G.El,accord f g (Lattice.gauge (fun _=>y) U) ∂G.probHaar)=_
    simp_rw [hu]
    exact (measurePreserving_mul_right G.probHaar y).integral_comp ((Homeomorph.mulRight y).measurableEmbedding) (fun g=>accord f g U)
  exact ⟨l, ⟨t,invariant_part ht.maps he⟩,he,ht⟩
end YM.Push.Mark
