import YM.Further.CURVED_GAUSSIAN_JETS.Gap
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Arcs
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Tinted
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Drums
/-!
 # withdraw stencil fee before density moments. exponential ratio value and cutoff λ support slack explicit. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Vacuum.Jets Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score
    AnalyticBridge.LocalGaussianLaws
open Planned.AtomRegular JointLoad JointLoad.Heir Heir.Carillon Push.SectorMeasure Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n r m : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G} {C : Libretto G n} {D : Record}
variable (a:Museum F x A X Y ι)(U:Config G f)
    (he: Plays C D P B Pt T x)(hf:B.Regular X f')(hτ:B.supBounds o X f' τ)(ho:o∈X)(hs: Short S B X)(hm: m+1 ≤ n)
    (hY: Walled S X Y x r)
variable (q d k) (Γ:Prices G ι→ℝ)(hu:0≤u)(hΓ:Silences G ι n u (D.ε*B.threshold) Γ)
local notation "z0"=> (1:Config G c)
local notation "f₀"=> deem o x T f'
local notation "d₀"=> P.dirBound (S.ratio.parent o)
set_option quotPrecheck false
local notation "f!"=> Complex.ofRealCLM ∘ f₀
lemma redacted {G:Gauge} {s:Side} {F H:Config G s→ℂ} {V} {m:ℕ} (hf:Multi.Puff.Crest m F V) (hx:Multi.Puff.Crest m H V) {l : List (Directions G s)}(hl:l.length≤ m):leftDerivs (F-H) l V=leftDerivs F l V-leftDerivs H l V:=by
    have he : Multi.Puff.Crest m ((-1:ℂ) • H) V:= into _ _ ((hx.germ).const_smul (-1:ℂ)); rw [sub_eq_add_neg F H, ← neg_one_smul ℂ H,Crest.sum_at l hl V hf he, scaled_left]; simp [sub_eq_add_neg]
section exact
omit [Fintype ι] [DecidableEq ι]
variable (F)
include he hf hτ F
lemma represented : Band n d₀ (1:Config G c) 1 (reachBill C τ) (f!):=by
   let f₁:=f₀; have hh:= deem_focus (o:=o) he hf
   have ht:= hτ.1; have hz:= patterns_nonneg n; have he₁:=C.matins; have he₂:=C.rights.large
   refine ⟨crest_cast.mpr hh,zero_le_one,(by unfold reachBill wealth; positivity),fun l hl hp=> ?_⟩
   rw [Push.Local.left_linear Complex.ofRealCLM l hh.germ hl];
   rw [one_pow,mul_one, show leftDerivs f₀ l z0= iteratedFDeriv ℝ l.length (f₀ ∘ journey z0 l.length l.get) 0 cart by simpa only [List.ofFn_get] using Germ.ordered l.get (hh.germ.of_le (Nat.cast_le.mpr hl))]
   rw [show ∀ u:ℝ, ‖Complex.ofRealCLM u‖=‖u‖ from fun _=> Complex.norm_real _]
   exact interpreted (F:=F) he hf hτ hl (fun i=> hp _ (List.get_mem ..)) l.length hl cart (fun i=> by apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro j; simp only [cart,Pi.single_apply]; split<;> norm_num)
end exact

local notation "p!"=> paint C D P B x
local notation "wi" => B.threshold
local notation "wj"=> (D.ε*B.threshold)
include he hf hτ hs hm hu hΓ ho hY
lemma hues (z: Prices G ι):
    let Z:= reachBill C τ; let a' :=paint C D P B x (u*‖tape z‖); let v:= B.threshold*pitch n _ D.Z (Heir.scope B X r x) P.power z
    let s:= Carillon.speed n D.Z B.threshold P.power (Heir.scope B X r x) z
    Band m (P.dirBound (S.ratio.parent o)) (1:Config G c) (s+1) (devBill C τ a'+ v*Z+‖Γ z-1‖ *Z) (a.concert T u q d k f' Γ U 1 z - (f!)):=by
   intro Z p v s
   let C':= f!
   have ht:= one_healthy (G:=G) Y _ P.threshold_pos.le; have hk:= he.cantos (k:=k) a ht hY ho; have hp := ivory hk B.threshold_pos.le B.threshold_le D.chimes z
   have hS:= hk.sing B.threshold_pos.le B.threshold_le D.chimes z
   have ha {F: Config G c→ℂ}{j v:ℝ}(h:Band n d₀ z0 j v F): Band m d₀ z0 j v F:=by
       have he := h.readable; have hk: ContDiffAt ℝ (m:WithTop ℕ∞) _ _:= he.germ.of_le (Nat.cast_le.mpr (Nat.le_of_lt hm))
       exact ⟨into m F hk,h.sane,h.nonneg,fun l hl=>h.caps _ (hl.trans (by omega))⟩
   have he' : Band m d₀ z0 1 Z C':= ha (represented (F:=F) he hf hτ)
   let f (V:Config G c):= f' (a.received k T q d u V U z)
   have hV :=hp.nonneg; have hZ:=he'.nonneg; have ht':=hτ.1; have hB : 1 ≤ s+1:= le_add_of_nonneg_left hp.sane; have hP:p≥0:=painting_pos C D P B x _ (mul_nonneg hu (norm_nonneg _)); have hd:0 ≤ devBill C τ p:=by have h:=C.matins; have h':=C.rights.large; unfold devBill wealth; have h:=patterns_nonneg n; positivity -- edit
   by_cases hy : z∈ tsupport Γ
   swap
   · have hq:= image_eq_zero_of_notMem_tsupport hy
     change Band _ _ _ _ _ (_ - C'); rw [show a.concert T u q d k f' Γ U 1 z=0 from funext (fun W=>by unfold Museum.concert; rw [hq]; simp)]; rw [zero_sub]; refine band_rise (band_rise (?_) (show ‖(-1:ℂ)‖*Z ≤ Z from by simp) le_rfl) ?_ hB
     · simpa only [neg_one_smul] using (he'.scale (-1))
     rw [hq,zero_sub,norm_neg,norm_one,one_mul]; exact le_add_of_nonneg_left (add_nonneg hd (mul_nonneg hV hZ))
   have h:=Peak.clue (q:=q) (d:=d) (k:=k) he a hf hu ht U z (hΓ.stay z hy)
   have hh:Germ n f z0:=ContDiffAt.comp (f:=fun p:Directions G c=>(p,z)) 0 h (contDiffAt_id.prodMk contDiffAt_const)
   have hX := Germ.prod hh (Nat.le_of_lt hm)
   let A:= Complex.ofRealCLM ∘ f
   have hx:Germ m A z0:= Complex.ofRealCLM.contDiff.contDiffAt.comp _ (show ContDiffAt ℝ m (f ∘ increment z0) _ from hX)
   have hb : Band m d₀ z0 1 (devBill C τ p) (A-C'):=by
       refine ⟨into m _ (hx.sub he'.readable.germ), zero_le_one,hd, fun l hl hU=>?_⟩
       let Q(l:ℕ):= Panels l
       have hv:=hl.trans (Nat.le_of_lt hm); have hξ:= (deem_focus (o:=o) he hf).germ
       rw [redacted (into m A hx) he'.readable hl]; unfold A C'; rw [Push.Local.left_linear Complex.ofRealCLM l (show Push.Local.Chart n f _ from hh) hv,Push.Local.left_linear Complex.ofRealCLM l (show Push.Local.Chart n f₀ _ from hξ) hv]
       rw [← map_sub,show ∀ x:ℝ, ‖Complex.ofRealCLM x‖ = ‖x‖ from fun _=>Complex.norm_real _]
       have h1(B:Config G c→ℝ)(h:Germ n B z0): leftDerivs B l z0 = iteratedFDeriv ℝ l.length (B ∘ journey z0 l.length l.get) 0 cart:=by simpa only [List.ofFn_get] using Germ.ordered l.get (h.prod hv)
       rw [h1 f hh,h1 _ hξ,one_pow,mul_one]
       have he:= imperfect (q:=q) (d:=d) (k:=k) he hf hs ho a U z hu (hΓ.stay z hy) hτ hv (fun i=>hU _ (List.get_mem l i)) _ (Nat.lt_of_le_of_lt hl hm) cart (fun i=> by apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro j; simp only [cart,Pi.single_apply]; split <;> norm_num)
       exact he
   let w := (Γ z:ℂ)
   have heq:=ha hS; let gZ(y:Config G c):ℂ:=Carillon.vary z0 (a.twilight k T) z y -- name conflict
   have hk:‖w‖≤1 := (Complex.norm_real _).trans_le (hΓ.little z)
   have hh: Band m d₀ z0 (s+1) (devBill C τ p) (w • (gZ*(A-C'))):=band_rise ((heq.multiply hb).scale w) (by rw [one_mul]; exact mul_le_of_le_one_left hd hk) le_rfl
   have hβ: Band m d₀ z0 (s+1) (v*Z) (w • ((gZ-(fun _=> (1:ℂ)))*C')):= band_rise (((ha hp).multiply he').scale w) (mul_le_of_le_one_left (mul_nonneg hV hZ) hk) le_rfl
   convert (band_plus (band_plus hh hβ) (band_rise (he'.scale (w-1)) (le_refl _) hB)) using 1
   · rw [show w-1=(Γ z-1:ℝ) from by simp [w], Complex.norm_real]
   ext1; simp [Museum.concert,gZ,A,C',w,f]; ring
end YM.PhysicalNext.Repeat.Cub
