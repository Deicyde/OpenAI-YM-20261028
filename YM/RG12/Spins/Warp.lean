import YM.RG12.Spins.Painter
import YM.RG12.Spins.Calorie
/-!
# Lift deck Hessian-sym pricing to isolated main primary leg on true c→f. Require
 unscaled pocket charter: F0 on link chart analytic at UNscaled width, zeroth and
 first derivatives vanish at link identity, and through fixed iso stamp uniform
 on THAT ball. Solar arrays d4 can use this with P0 unscaled `column i`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Spins
open Next.Foundations
open Function Filter Set Lattice Wilson Pressure RG Push.SectorMeasure
open Multi Multi.Vacuum.Jets Multi.Puff WardBin.Lies
open PhysicalNext.JointLoad.Heir PhysicalNext Next Next.SectorChange Next.SectorChange.Rows Wisps Next.Fluctuations AnalyticBridge.SectorAffine.Offset AnalyticBridge.LocalGaussian.Moments
open Finset Planned.AtomRegular Foliage MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{t:ℝ}{I:Type}[Fintype I][DecidableEq I]{p n r:ℕ}{P B:BudgetPoint}{c f:Side}{o: Site f}{A K C γ u d x:ℝ}
variable {S:StepData c f}{T:Tube G S}{Pt:Teller G}{L:Tree.Forest S.ratio}{b:S.Choices}{q χ:Chi}{X:Support f}{Y:Support c}{A₀: Stores S}
   (m:Museum L x A₀ X Y I)(U:Config G f){C':Libretto G p}{D:Record}
   (hb:Plays C' D P B Pt T x)
   {J: Config G f→ℝ}(hf:B.Regular X J)(ho:o∈X)(hs:PhysicalNext.JointLoad.Heir.Short S B X)
variable {F:Deck G c f→ℂ}
set_option quotPrecheck false
local notation "ψs" => S.ratio.parent o
local notation "c_0" => reach x
local notation "ψd" => Cube.fee C'.Z
local notation "R₁" => loom P (c_0) (ψd)
local notation "σ₀" z => m.extra (1:Site c→G.El) u z
local notation "ωΩ" z => ((0,σ₀ z):Deck G c f)
local notation "ΩF" z => (fun W=> ((J (m.received b T q d u W U z)):ℂ))
local notation "ρ" => PhysicalNext.JointLoad.Heir.crop (ψs) (c_0) (1:Site c→G.El)
noncomputable def pivotRay (G:Gauge){c f:Side}(F:Deck G c f→ℂ)(t:ℝ)(o:Site c)(r:ℕ)(x:Deck G c f) (W:Config G c):ℂ:= (t^2)⁻¹ • F ((PhysicalNext.JointLoad.Heir.crop o r 1 W,0)+x)
local notation "wallX" => pivotRay G F P.threshold (ψs) (c_0)
include hb hf ho hs
omit [DecidableEq I] in
set_option maxHeartbeats 640000 in
lemma warped (hu:0<u)(hn:4 ≤ p)
    (hF:∀ a, ‖a‖≤ (R₁) → Through 4 F a A)(hEq:∀ a:Deck G c f, F a = P.threshold^2 • ((J (increment 1 (display T L x b true a)):ℝ):ℂ)) (z:Prices G I)
    (hχ: z∈tsupport (PhysicalNext.JointLoad.Heir.guard χ G I u (D.ε*B.threshold))):
      let K:= ψd*((1+((reach x:ℕ):ℝ))^(P.power*p))
      Crest 2 (ΩF z) 1 ∧ Band 2 (P.dirBound (ψs)) (1:Config G c) P.threshold ((A*(Planned.AtomRegular.patterns 2)* K^2)*((powers z*u)^2)/P.threshold^2) ((Noise.half (ΩF z) (ΩF (-z))) - wallX 0):=by
    intro Cq
    have hT:=hb.rehearsed
    have hs':= Repeat.Cub.posed C'.Z hT.wire (o:=ψs)
    have hC:1 ≤ ψd:= Cube.fee_one ..; have hl:0<B.threshold:= B.threshold_pos; have hp:=P.threshold_pos; have hr:=D.guards
    have hq : 1 ≤ Cq:= one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ (by exact le_add_of_nonneg_right (Nat.cast_nonneg _)))
    let Γ:=PhysicalNext.JointLoad.Heir.guard χ G I u (D.ε*B.threshold)
    let g (z:Prices G I): Config G c → ℂ:= ΩF z
    let i (z:Prices G I):Deck G c f:= ωΩ z
    have hz' : -z ∈ tsupport Γ := by
       have HE (j): Γ (-j)=Γ j:=Noise.even_guard χ u (D.ε*B.threshold) j
       by_contra ht
       have ht:= (show ContinuousAt (- · : Prices G I→ Prices G I) z by fun_prop).eventually (notMem_tsupport_iff_eventuallyEq.mp ht)
       exact ((notMem_tsupport_iff_eventuallyEq.mpr (ht.mono (fun j hj=> by change Γ j=0; rw [← HE j]; exact hj))) : z∉ tsupport Γ) hχ
    have hFz:= guard_silent χ (G:=G) (I:=I) (n:=p) hu (mul_pos hr hl)
    have h0:= one_healthy (G:=G) Y _ hp.le
    let launch0:= instill G c f (ψs) (c_0)
    have hX (z:Prices G I)(hz:z ∈ tsupport Γ): ‖i z‖ ≤ R₁ ∧ Crest 2 (g z) 1 ∧ ∀ j (v: Slab G c j), g z ∘ journey 1 j v =ᶠ[𝓝 0] (wallX (i z)) ∘ journey 1 j v :=by
       have ht:= hFz.stay z hz
       have hw: ‖σ₀ z‖ ≤ R₁:= (m.extra_size _ u hu.le z).trans (ht.trans hT.tensions.noise)
       have hr:0≤ R₁:=(norm_nonneg _).trans hw
       refine ⟨max_le (by change ‖(0:Directions G c)‖ ≤ _; simpa only [norm_zero] using hr) hw,?_,fun j v=>?_⟩
       · have HE:= Repeat.Peak.clue (q:=q) (d:=d) (k:=b) hb m hf hu.le h0 U z ht
         refine into 2 _ (by apply ContDiffAt.comp (g:=Complex.ofRealCLM) (f:=fun y:Directions G c=> J (m.received b T q d u (increment 1 y) U z)) 0; · exact Complex.ofRealCLM.contDiff.contDiffAt
                             exact ((HE.comp (f:=fun y:Directions G c=> (y,z)) 0 (contDiffAt_id.prodMk contDiffAt_const)).of_le (Nat.cast_le.mpr (by omega :2 ≤ p))))
       have hi:= depicted (q:=q) (d:=d) m hb.bulletin hT.weft (hb.acts L b) hs hs' ho hC hT.tensions.allows U z hw v
       filter_upwards [hi] with y hy
       change (↑(J (m.received b T q d u _ U z)):ℂ)= (wallX _) _
       simp only [pivotRay,hEq,smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hp.ne'),one_smul]; congr 1
       have hv:=(hf.sites _ _ (agrees_mono hy (fun _ H=> Finset.mem_union_left _ H))).trans ((hf.symmetry _ _).trans (hf.symmetry ..))
       change J _ = J _
       convert hv.symm using 2 ; simp [i,enters,PhysicalNext.JointLoad.Heir.launch]
    let w:= i z
    obtain ⟨hW,hG,hb'⟩:= hX z hχ; obtain ⟨_,hG',hc⟩:= hX (-z) hz'
    have hq₀ : i (-z)=-w:=by ext1 <;> simp [i,w]
    have hφ(j:ℕ)(v:Slab G c j)(hj:j≤2)(hv:∀ i,P.dirBound (ψs) (v i)) := floor_rate (f:=f) hs' hC v hv (show j ≤ p from by omega)
    have hV (a:Deck G c f)(ha:‖a‖ ≤ R₁):Crest 2 (wallX a) 1:= by
       let H (y:Directions G c):Deck G c f:= (ρ (increment 1 y),0)+a
       have he:H 0=a:=by simp [H, PhysicalNext.Repeat.Cub.blankBirth]
       have hm: ContDiffAt ℝ 2 H 0:= ContDiffAt.add (((hs'.germ.of_le (by exact le_top)).prodMk contDiffAt_const)) contDiffAt_const
       have hg:ContDiffAt ℝ (↑(2:ℕ)) F (H 0):=he.symm ▸ (hF a ha).smooth.of_le (by norm_num)
       exact into _ _ ((hg.comp (f:=H) 0 hm).const_smul _)
    have ht : ‖w‖ ≤ powers z*u:=max_le (by change ‖(0:Directions G c)‖ ≤ _; rw [norm_zero]; exact mul_nonneg (powers_pos z).le hu.le) ((m.extra_size _ u hu.le z).trans ((mul_le_mul_of_nonneg_left (Lute.tape_control z).2 hu.le).trans_eq (mul_comm ..)))
    have hR:0 ≤ R₁:=(norm_nonneg _).trans hW
    have hh := attend F w launch0 (wallX) hR hp (powers_pos z).le (le_refl 4) hF hW ht hu.le hq (V:=P.dirBound (ψs)) (n:=2) (by
        intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl | rfl <;> apply hV
        · exact hW
        · rw [norm_neg]; exact hW
        simpa) (by
        intro j v hj hv; obtain ⟨ht,hw,hJ⟩:=hφ j v hj hv; exact ⟨ht,hw,hJ,fun x _=> Eventually.of_forall (fun _=>rfl)⟩)
    have hZ:Crest 2 ((Noise.half (ΩF z) (ΩF (-z))) - wallX 0) (1:Config G c):=into _ _ (((hG.germ.add hG'.germ).const_smul (1/2:ℂ)).sub (hV 0 (by simpa)).germ)
    refine ⟨hG,hZ,hp.le,hh.nonneg,fun l he hv=> le_trans ?_ (hh.caps l he hv)⟩
    have hl (f g: Config G c→ℂ)(hf:Crest 2 f 1)(hg:Crest 2 g 1)(hx:f∘journey 1 l.length l.get=ᶠ[𝓝 0] g∘journey 1 _ l.get): leftDerivs f l 1=leftDerivs g l 1:=by
       have H(y:Config G c→ℂ)(hy:Crest 2 y 1):=Germ.ordered l.get (f:=y) (show Germ _ _ _ from hy.germ.of_le (Nat.cast_le.mpr he)); simp only [List.ofFn_get] at H; rw [H _ hf,H _ hg,(hx.iteratedFDeriv (𝕜:=ℝ) _).eq_of_nhds]
    refine le_of_eq <| congr_arg _ <| hl _ _ hZ hh.readable ?_
    filter_upwards [hb' l.length l.get,hc l.length l.get] with y hx ha
    rw [hq₀] at ha
    change g z _ = (wallX w) _ at hx; change g (-z) _ = (wallX (-w)) _ at ha
    exact congr_arg₂ (fun x y'=>(1/2:ℂ)*(x+y')-_) hx ha
end YM.RG12.Spins
