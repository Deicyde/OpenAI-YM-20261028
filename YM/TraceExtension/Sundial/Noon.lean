import YM.TraceExtension.Sundial.Shade

/-! A position coupling through this parity-even horizon. Can even give a
 real Big-O variant in this prescription. Uses E derivative at a separated
 pair (spatial-time Ward determinant test; no exact energy label as input).
 Square variable with odd sign branch, compare to actual Wilson coupling.
 IMPORTANT the normalization is independently proved for Wilson FIRST. It
 would not prove the Wilson-normalized relation simply to choose the reading
 and solve the Ward equations in the new coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Sundial
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace MergeProof.East MeasureTheory Pilot Pith
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{X:Extraction.Order}
variable {S:Table C.book}(F: Final C X S)(H:(Bel C.book).Hierarchy)
local notation "F₀"=> Bel C.book
variable (h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{Z:Arch C} (hp:Bliss F 𝓛 Z H)
variable {P P':ℝ→change S 4}(hP:PlotX F H 𝓛 h P)(hQ:∀ m:ℕ,∀ᶠ r in trail, chores r (P r) m)
variable {χ:E4→ℝ}{x y:ℝ→ℝ}(p:Posed H h P P' x y)(q: ShellNorm P' χ)
open Asymptotics
/-- Tangent detector slope: before definition of the coupling used here. -/
def bauble(C:Family G):ℝ := (-d2 G)*(datum C).re
lemma cab(h:G.Simple)(H:(Bel C.book).Hierarchy): bauble C≠0:= mul_ne_zero (neg_ne_zero.mpr (force_neg h).ne) (dato H h)

def lampX (P:ℝ→change S 4)(t:ℝ):= (E P t).re / bauble C
def glo (P:ℝ→change S 4) (i:ℝ):= Real.sqrt (lampX P i)
include F hp hP hQ
variable {g:ℝ→ℝ}(hg: Coupling G g)
include hg
lemma beryl:Tendsto (fun i=> (E P i).re/g i^(2:ℕ)) trail (𝓝 (bauble C)):=by
   obtain ⟨w,hw⟩:= margaret F h hp _ hP; obtain ⟨κ,e,hK,hχ,hμ,Hf⟩:= formed H F h hg hw hP hQ
   obtain ⟨τ,hτ⟩:=Work.A05.has_window sail sail_at
   let c:= datum C; have ht:= eid H F h hg hw hP hτ (Hf τ hτ|>.1) hQ ; have hx:= Complex.continuous_re.continuousAt.tendsto.comp ht; simp only [Function.comp_def, Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero, div_eq_mul_inv] at *; exact hx.congr fun i=>mul_comm ..
include p q
lemma brighter : Tendsto (fun i=> (E P' i).re/g i^(2:ℕ)) trail (𝓝 (bauble C)):=by
   obtain ⟨hx,hy⟩:= anneal F H h hp hP hQ q.valid p q; have hw:= (hy.mul hx).mul (beryl F H h hp hP hQ hg);rw [one_mul,one_mul] at hw; refine hw.congr' ?_; filter_upwards[ethane F H h hp hP hQ q.valid p q] with i hi; rw [hi]; simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero];ring
lemma reforest : Tendsto (fun i=>lampX P' i/g i^(2:ℕ)) trail (𝓝 1):=by
   have hz:= brighter F H h hp hP hQ p q hg; have ht:= hz.div_const (bauble C); rw [div_self (cab h H)] at ht; exact ht.congr fun i=>by unfold lampX; ring
lemma glow : (∀ᶠ i in trail,0<lampX P' i)∧Tendsto (fun i=> glo P' i/g i) trail (𝓝 1)∧ Coupling G (glo P'):=by
   let f:= lampX P'; let v:=glo P'; have hx:= reforest F H h hp hP hQ p q hg ; have he : ∀ᶠ i in trail, 0<f i:=by
      filter_upwards [hx.eventually (lt_mem_nhds zero_lt_one),hg.positive] with i hi hu; change 0 < f i/g i^2 at hi; have hh:= (lt_div_iff₀ (pow_pos hu 2)).1 hi; rwa [zero_mul] at hh
   have hp : ∀ᶠ i in trail, v i^2=f i:= he.mono fun i hi=>Real.sq_sqrt hi.le; have hh:= hg.running.mul hx; rw[mul_one] at hh
   refine ⟨he, ?_, (he.mono fun i hi=>Real.sqrt_pos.mpr hi),hh.congr' ?_⟩
   · have ht:= hx.sqrt;rw [Real.sqrt_one] at ht; apply ht.congr'; filter_upwards[he,hg.positive] with i hi hu
     rw [Real.sqrt_div hi.le,Real.sqrt_sq hu.le];rfl
   filter_upwards[he,hg.positive,hp] with i hi hu hV; change LogV _*g i^2*(f i/g i^2)=LogV i*v i^2;rw[hV, mul_assoc, mul_div_cancel₀ _ (pow_ne_zero _ hu.ne')]

lemma meterQ : ∃ (a d e:ℝ→ℝ), TendC F P' d ∧ Tendsto a trail (𝓝 1)∧ (∀ᶠ r in trail, Pith.Measures F r (P' r) (a r) (d r) (e r)) ∧ (fun i=> d i-d2 G*(glo P' i)^ (2:ℕ)) =O[trail] fun i=>(glo P' i)^ (4:ℕ):=by
   let f:=lampX P'; let v:=glo P'; obtain ⟨hL,hK,hV⟩:=glow F H h hp hP hQ p q hg
   obtain ⟨w,hw⟩:= margaret F h hp _ hP
   have hh:= avatar F H h hp hP hQ q.valid p q; obtain ⟨d,hD,-⟩:=across F h hp P P' hP hh w hw
   have hx:Tendsto (fun t=> d t/v t^ (2:ℕ)) trail (𝓝 (d2 G)):=by rw[force_b]; exact hD.measures v hV
   let Θ(s:ℝ)(c:ℝ×ℝ):= Pith.Measures F s (P' s) c.1 (d s) c.2; let e(s:ℝ):=if h:∃ c,Θ s c then h.choose else 0; let a(s):=(e s).1
   have he : ∀ᶠ i in trail,Θ i (e i):= hD.tensor.mono fun i hi=>by
      have he :∃ c,Θ i c:=by
           obtain ⟨a,e,ht⟩:=hi; refine ⟨(a,e),{reads:=fun j k=>?_}⟩; rw[ht]; dsimp only; by_cases hv:j=k<;> simp[Pith.erase,hv,add_assoc]
      unfold e; rw[dif_pos he]; exact he.choose_spec
   have hu: LiveP P' a d χ:=by
      constructor
      · filter_upwards[he,hh.spun,self_mem_nhdsWithin] with i hi hz ht; exact (Pith.translates F hi _ sail_at ht q.valid hz.align.unit timeAxis _ (Pith.dial C)).trans (Pith.div_cross F _ sail_at ht _ _ _).symm
      filter_upwards[he,hh.spun,self_mem_nhdsWithin] with i hi hz ht using Pith.conserv F hi _ sail_at ht hz.align.unit (Pith.dial C) timeAxis
   let C' := bauble C; let H':= fun i=> (Q P' χ i).re; let b:= (datum C).re; have hb:b≠0:= dato H h; let K:=(prism C χ).re
   have hΦ : Tendsto H' trail (𝓝 K):= Complex.continuous_re.continuousAt.tendsto.comp (crystals F H h hp hP hQ q.valid p q)
   have hC: ∀ᶠ i in trail,(a i-1)=-d i*H' i/b ∧ d i=d2 G * (v i^2)*a i:=by
       filter_upwards[q.swings,hu.normalization,hu.conservation,hL] with i hi hv hu hx; have hp:= congr_arg Complex.re hv; have hm:= congr_arg Complex.re hu
       simp only[Complex.add_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hi.1,hi.2,Complex.zero_re] at hp hm
       have ht: (E P' i).re=f i* C':= (div_mul_cancel₀ _ (cab h H)).symm; have he:v i^2=f i:= Real.sq_sqrt (le_of_lt hx)
       change a i*(E P' i).re+d i*b=0 at hm; change a i*b+d i*H' i=b at hp
       rw[ht] at hm; change a i*(f i*(-d2 G * b))+ _=_ at hm
       refine ⟨?_,?_⟩
       · rw [eq_div_iff hb];linarith only[hp]
       rw [he]; apply mul_right_cancel₀ hb; linarith only [hm]
   have hs : Tendsto (fun i=> (a i-1)/v i^2) trail (𝓝 (-(d2 G)*K/b)):=by
       have hv:=(hx.neg.mul hΦ).div_const b; apply hv.congr'; filter_upwards[hC] with i hi; rw[hi.1]; ring
   have hA: Tendsto a trail (𝓝 1):=by
       have he:= (hs.mul ((hV.conforms h).pow 2)).add_const 1; rw [zero_pow (by norm_num),mul_zero,zero_add] at he; apply he.congr'; filter_upwards[hV.positive] with i hi; change (a i-1)/v i^2*v i^2+_= _; have hp:v i≠0:=hi.ne'; field_simp; ring
   let c:= d2 G; refine ⟨a,d,Prod.snd ∘ e,hD,hA,he,?_⟩
   have hO:Tendsto (fun i=>(d i-c*v i^2)/v i^4) trail (𝓝 (c*(-(d2 G)*K/b))):=by
       apply (hs.const_mul c).congr'; filter_upwards[hV.positive,hC] with i hi hu; change c*((a i-1)/_)=_; have he : v i≠0:=hi.ne'; rw[hu.2]; unfold c; field_simp; ring
   have hb:=hO.norm.eventually (ge_mem_nhds (lt_add_one ‖c*(-(d2 G)*K/b)‖)); refine isBigO_iff.mpr ⟨‖c*(-(d2 G)*K/b)‖+1,?_⟩; filter_upwards[hb,hV.positive] with i hi hu
   change ‖_/ (v i)^4‖ ≤ _ at hi; rw[norm_div] at hi; exact (div_le_iff₀ (norm_pos_iff.mpr (pow_ne_zero _ hu.ne'))).1 hi
end YM.Trace.Sundial
