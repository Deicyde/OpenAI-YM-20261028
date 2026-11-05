import YM.TraceExtension.Quince.Cash
/-! # Stochastic minus route at reference phase. one more derivative than order being sampled. In a genuine Neighborhood. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure Planned.AtomRegular MultiNext.SignedSource WardBin.Lies Foliage
open JointLoad JointLoad.Heir Lyre
open Cub
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {F : Forest S.ratio}
    {P B : BudgetPoint} {X : Support f} {Y : Support c} {t r x τ : ℝ} {I : Type}
    {A : Stores S} {n j l : ℕ} {D' : Slab G c l} {u : ℝ} {q : Chi} {d : ℝ} {f' : Config G f → ℝ}
    {o : Site f}{C : Libretto G n}{D : Record}
variable (h : Plays C D P B Pt T x)
local notation "V₀"=> (1:Config G c)
local notation "G₀"=> (1:Site c→G.El)

-- Plan function along true V. Unmasked ENERGY approximation evidence. Does not replace masks in eventual maps.
abbrev dimW (o: Site f)(q: ℕ)(T:Tube G S)(F:Config G f→ℝ): Config G c→ℝ:= F ∘ increment (1:Config G f) ∘ (Heir.route T) ∘ (Heir.crop (S.ratio.parent o) q 1)
variable {m:ℕ}
section booths
variable (F)
variable (hf:B.Regular X f')(hτ:B.supBounds o X f' τ)
    (hl:l ≤ n)(hU:∀ i,P.dirBound (S.ratio.parent o) (D' i))
include h hf
lemma dimW_focus :Multi.Puff.Crest n (dimW o m T f') 1 :=by
  apply Multi.Puff.into
  have hc:=h.rehearsed; have hp:Canvas P (S.ratio.parent o) m V₀ G₀ n C.C:= posedW C.Z
  have he := ContDiffAt.comp (g:=Heir.route T) 0 (Heir.route T).contDiff.contDiffAt hp.germ
  have hy:(((Heir.route T) ∘ (Heir.crop (S.ratio.parent o) m (1:Site c→G.El) ∘ increment 1)) (0:Directions G c))=0:=by simp only [Function.comp_apply,Work.G07.at_zero_increment, blankBirth,map_zero]
  exact (show ContDiffAt ℝ n (f' ∘ increment 1) _ from hy.symm ▸ (hf.smooth 1 (one_healthy X _ B.threshold_pos.le)).of_le (Nat.cast_le.mpr hc.orders)).comp _ (he.of_le le_top)
variable (hzz:Until C D P B S o X Y m x)
include F hl hU hτ hzz
lemma dimWord (j: ℕ) (hj:j ≤ n) (v: Fin j → Panels l)(hv: ∀ i, ‖v i‖ ≤ 1):
    ‖iteratedFDeriv ℝ j (dimW o m T f' ∘ journey 1 l D') 0 v‖ ≤ reachBill C τ:=by
  have hc:=h.rehearsed; have hp:Canvas P (S.ratio.parent o) m V₀ G₀ n C.C:=posedW C.Z
  let f:= f' ∘ increment (1:Config G _); let U:=lotW o m T l D'
  have hT : U 0=0:=lotW_zero m
  have hY:ContDiffAt ℝ n U 0:= (Heir.route T).contDiff.contDiffAt.comp _ (hp.ready D')
  have he':ContDiffAt ℝ n f (U 0):= by rw [hT]; exact (hf.smooth 1 (one_healthy X _ B.threshold_pos.le)).of_le (Nat.cast_le.mpr hc.orders)
  have ht:= hτ.1; have hr:=C.rights.large; have hZ:1 ≤ wealth C:= by unfold wealth; linarith [C.matins]
  change ‖iteratedFDeriv ℝ j (f ∘ U) 0 v‖ ≤ _
  have hv': (∏ i,‖v i‖) ≤ 1:= Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun _ _=>hv _)
  apply le_trans ((ContinuousMultilinearMap.le_opNorm ..).trans (mul_le_of_le_one_right (norm_nonneg _) hv'))
  apply slots_bound hY he' hj (by positivity :0≤(wealth C)^n*C.rights.fee*τ) (fun p v hv=>?_)
  rw [hT]; let k:=p.length; have hk:= p.length_le.trans hj
  apply (C.rights.born _ _ (fun _=> wealth C) hk (hk.trans hc.orders) hf hτ (one_healthy X _ B.threshold_pos.le) (fun i=>opticW F h m hzz.low hzz.small hl hU _ ((p.partSize_le i).trans hj) _ (fun j=>hv _))).trans
  simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin]; gcongr
end booths
section canvas
variable [Fintype I] (hf:B.Regular X f')(hzz:Until C D P B S o X Y m x)(ho:o∈X)
    (a: Museum F x A X Y I) (U:Config G f)(w:Prices G I)(hu:0≤u)(hw:u*‖tape w‖ ≤ D.ε*B.threshold)
    (hτ:B.supBounds o X f' τ)(hl:l ≤ n)(hU:∀ i,P.dirBound (S.ratio.parent o) (D' i))
include h hf hτ hzz hu hw hl hU
lemma imperfectW (j:ℕ)(hj:j+1≤ n)(v:Fin j → Panels l) (hv:∀ i, ‖v i‖ ≤ 1): let F₁:=fun q'=>f' (a.received k T q d u q' U w); let g := journey 1 l D'; let f₀:=dimW o m T f'
    ‖iteratedFDeriv ℝ j (F₁ ∘ g) 0 v - iteratedFDeriv ℝ j (f₀ ∘ g) 0 v‖ ≤ devBill C τ (paintW C D P B m (u*‖tape w‖)) :=by
  intro f₁ g f₀; have hc:=h.rehearsed; have hT:=hc.tensions; have hZ := C.C_one; have hD:= D.majorant
  have hV: Canvas P (S.ratio.parent o) m V₀ G₀ n C.C:=posedW C.Z
  have hn : 2≤n:=by have he:= hc.test; have hh:=P.order_ge; omega
  have hF := (h.acts F k)
  let σ:= a.extra G₀ u w
  have hw₂:= a.extra_size G₀ u hu w; have hw₁: ‖σ‖ ≤ loom P (reach x) C.C:= hw₂.trans (hw.trans hT.noise)
  have hz:= hT.allows; have hb:=hT.small.trans (min_le_right ..)
  have hΥ:=border_healthy h.sew C.width C.price hc.early hF hD hn hT a h.bulletin C.Z rfl hc.wire h.space hc.temp_eq (one_healthy _ _ P.threshold_pos.le) U w hu hw B.threshold_pos (q:=q) (d:=d)
  have ht:=hτ.1; have he:= mul_nonneg hu (norm_nonneg (tape w))
  let d0:=paintW C D P B m (u*‖tape w‖); have hd: d0≥0:=painted C D P B m _ he
  let W:=wealth C; have hW:1≤ W:=by unfold W wealth; linarith [C.matins]
  let w0:=W+d0; have hk:1 ≤ w0:=hW.trans (le_add_of_nonneg_right hd); have hm : d0≤ w0:= le_add_of_nonneg_left (zero_le_one.trans hW)
  let f0:=lotW o m T l D'; let f:= display T F x k true ∘ enters V₀ (S.ratio.parent o) m G₀ D' σ
  let M:= f' ∘ increment (1:Config G _); have hy:f0 0=0:=lotW_zero m; have hr:=C.rights.large
  have h₁: M ∘ f =ᶠ[𝓝 0] f₁ ∘ g:=by
     filter_upwards [depictedW (q:=q) (d:=d) (k:=k) h hzz a U w hw₁ l D'] with u₀ hv
     exact (hf.sites _ _ (agrees_mono hv (fun _ h=> Finset.mem_union_left _ h))).trans ((hf.symmetry _ _).trans (hf.symmetry ..))
  obtain ⟨hx,hG⟩:= pluckedW h hzz a U w hw₁ D' hΥ
  have h0: ContDiffAt ℝ n M (f0 0):=by rw [hy]; exact (hf.smooth 1 (one_healthy X _ B.threshold_pos.le)).of_le (Nat.cast_le.mpr hc.orders)
  have hp : Healthy B.threshold X (increment 1 (f 0)):=by simpa only [one_smul,f,σ,Function.comp_apply] using hG 1 (by simp)
  have h' := (Heir.along hf hp).of_le (Nat.cast_le.mpr hc.orders); have hu₁: ‖σ‖≤ loom P m C.C:= hw₁.trans (by unfold loom; gcongr<;>first|exact hzz.tall| have hQ:=P.threshold_pos; positivity)
  have hA:= (timesEnter hV hF hc.temp_eq hn hU hZ hl hD ((le_mul_of_one_le_left ((norm_nonneg _).trans hu₁) hD).trans hzz.small) hzz.normP.le hu₁ true).1
  have hy':ContDiffAt ℝ n f0 0:= (Heir.route T).contDiff.contDiffAt.comp _ (hV.ready D')
  have hC : (j:ℕ∞ω) ≤ n:= Nat.cast_le.mpr (Nat.le_of_lt hj)
  have he₁ {i:ℕ}(hi:i≤n)(v:Fin i→ Panels l)(hp:∀ j, ‖v j‖ ≤ 1):= earnW (F:=F) (k:=k) h m hzz.low hzz.small hzz.normP hl hU hi v hp hu₁ hw₂
  have h₂:Sized d0 (f 0) B o:=by
     have hz: Sized d0 ((iteratedFDeriv ℝ 0 f 0 0)-(iteratedFDeriv ℝ 0 f0 0 0)) B o:= he₁ (Nat.zero_le _) _ (fun i=> i.elim0)
     simpa only [iteratedFDeriv_zero_apply,hy,sub_zero] using hz
  rw [← (h₁.iteratedFDeriv (𝕜:=ℝ) j).eq_of_nhds]; change ‖iteratedFDeriv ℝ j (M∘f) 0 v - iteratedFDeriv ℝ j (M∘f0) 0 v‖ ≤ _
  rw [iteratedFDeriv_comp h' hA hC,iteratedFDeriv_comp h0 hy' hC]; simp only [FormalMultilinearSeries.taylorComp, sum_apply,←Finset.sum_sub_distrib]
  let p' := (1+(2:ℝ)^n)*(d0*w0^n*C.rights.fee*τ); have hp':0≤p':=by unfold p'; positivity
  refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=>p') (fun p _=>?_)).trans ?_)
  · let X₀:=iteratedFDeriv ℝ p.length M (f 0); let V (i:Fin p.length):= iteratedFDeriv ℝ (p.partSize i) f 0 (v ∘ p.emb i); let V₀' (i:Fin p.length):= iteratedFDeriv ℝ (p.partSize i) f0 0 (v ∘ p.emb i)
    have hQ(i:Fin p.length):= (p.partSize_le i).trans (Nat.le_of_lt hj); have hθ : p.length+1 ≤ n:= Nat.lt_of_le_of_lt p.length_le hj
    have hV i:Sized d0 (V i-V₀' i) B o:=he₁ (hQ i) _ (fun i=>hv _)
    have hM i:Sized W (V₀' i) B o:=opticW F h m hzz.low hzz.small hl hU _ (hQ i) _ (fun i=>hv _)
    have hV' i:Sized w0 (V i) B o:= by
       refine ⟨zero_le_one.trans hk,fun t=>?_⟩
       apply (norm_le_add (V i t) (V₀' i t)).trans
       exact (add_le_add (hV i|>.2 t) (hM i|>.2 t)).trans_eq (by unfold w0; ring)
    change ‖X₀ V-iteratedFDeriv ℝ p.length M (f0 0) V₀'‖ ≤ _; rw [hy]; exact migrant C.rights hf hτ h₂ hV' hk hθ hc.orders hx hG hV (fun i=>higher (hM i) (le_add_of_nonneg_right hd)) hm
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]; exact mul_le_mul_of_nonneg_right (card_le_patterns (Nat.le_of_lt hj)) hp'
where
  norm_le_add (a b:G.Color):‖a‖ ≤ ‖a-b‖+‖b‖:=by simpa using norm_sub_le_norm_sub_add_norm_sub a b 0
end canvas
end YM.PhysicalNext.Repeat.Quince
