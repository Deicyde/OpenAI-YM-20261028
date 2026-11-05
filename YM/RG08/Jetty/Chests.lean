import YM.RG08.Jetty.Bank

/-! # Fixed-order moment including addresses

The bridge to polynomial prices. Include paths in Loom (or simply compose
with this estimate with length dominated as in canonical choices). The two
measures represent a signed derivative valuation, at each tape and jet. See
concert. No infimum which silently dropped the test charges. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Jetty
open Forms Pert.Bulk RG Function Finset MeasureTheory Filter
open scoped Topology ENNReal Classical BigOperators ContDiff
variable {I:Type}{l:Loom I}{d u n:ℕ}{σ B:ℝ}{h:0<σ}
variable {F:Pack n I}

def trunk (l:Loom I)(u:ℕ)(x:Tape n I)(w:E4):ℝ:= (1+ ∑ i,l.height (x i)+‖w‖)^u
lemma trunk_nn (x:Tape n I)(w:E4):0 ≤ trunk l u x w:=by
 have ht:= Finset.sum_nonneg (s:=univ) (f:=fun i:Fin n=>l.height (x i)) (fun i _=>l.nn _)
 unfold trunk; positivity

def Crew (d:ℕ)(σ:ℝ)(F:Pack n I)(μ ν:Tape n I→Jet d→Measure E4):Prop:=
 (∀ x s, IsFiniteMeasure (μ x s)∧IsFiniteMeasure (ν x s)∧Integrable (Beacon σ) (μ x s)∧Integrable (Beacon σ) (ν x s))∧
 ∀ x f, (∀ s, Integrable (fun w=>openJet s w f) (μ x s) ∧ Integrable (fun w=>openJet s w f) (ν x s))∧ F x f=∑ s,((∫ w,openJet s w f ∂μ x s)-(∫ w,openJet s w f ∂ν x s))

def tithe (l:Loom I)(u d:ℕ)(μ:Tape n I→Jet d→Measure E4)(x:Tape n I):ℝ:=∑ s,(∫ w,trunk l u x w ∂μ x s)

-- explicit (σ fixed pre-L but can shrink with schedules).
def blade (n u:ℕ)(σ:ℝ):ℝ:= (((1+n:ℕ):ℝ) * (1+(u:ℝ)/σ)) ^ u
lemma blade_nn (n u:ℕ)(h:0≤σ):0≤blade n u σ:=by unfold blade;positivity
lemma trunk_bound (u:ℕ)(x:Tape n I)(w:E4)(h:0<σ):trunk l u x w ≤ blade n u σ * Real.exp (σ*l.cage x)*Beacon σ w:=by
 let r:= l.cage x; let y:= ‖w‖; have hr:=l.cage_nn x; change 0≤r at hr; have hy:0≤y:= norm_nonneg _
 unfold trunk blade Beacon
 rw [mul_assoc,← Real.exp_add]
 let a:ℝ:=1+n
 have hh : ∑ i,l.height (x i) ≤ n*r:= (sum_le_sum (fun i _=> l.float x i)).trans_eq (by rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul])
 have Hn : 0 ≤ (n:ℝ) := by positivity
 rcases Nat.eq_zero_or_pos u with hz|hz
 · subst u; simp only [pow_zero,one_mul];change 1 ≤ Real.exp (σ*r+σ*y);exact Real.one_le_exp (by nlinarith)
 have hu:0<(u:ℝ):= Nat.cast_pos.mpr hz
 let b:= σ*(r+y)/(u:ℝ)
 have hb:1+b≤Real.exp b:= by rw [add_comm];exact Real.add_one_le_exp _
 push_cast
 change _≤ (a*(1+(u:ℝ)/σ))^u * _
 rw [show σ*l.cage x+σ*‖w‖=(u:ℝ)*b from by unfold b;field_simp; ring, Real.exp_nat_mul,← mul_pow]
 apply pow_le_pow_left₀
 · linarith [sum_nonneg (s:=univ) (f:=fun i=>l.height (x i)) (fun i _=>l.nn _),norm_nonneg w]
 refine LE.le.trans (b:=a*(1+(u:ℝ)/σ)*(1+b)) ?_ (mul_le_mul_of_nonneg_left hb (by unfold a;positivity))
 have he : 1+r+y ≤ (1+(u:ℝ)/σ)*(1+b):=by unfold b;field_simp; nlinarith [mul_nonneg h.le (add_nonneg hr hy)]
 change 1+_+y ≤ _
 have hx : 1+∑ i,l.height (x i)+y ≤ a*(1+r+y):=by unfold a; nlinarith only [hr,hy,Hn,mul_nonneg Hn hy, hh]
 rw [mul_assoc];exact hx.trans (mul_le_mul_of_nonneg_left he (by unfold a;positivity))

lemma dues {μ: Measure E4}(hi:Integrable (Beacon σ) μ)(u:ℕ)(h:0<σ)(x:Tape n I):
 Integrable (trunk l u x) μ ∧ (∫ w,trunk l u x w ∂μ) ≤ blade n u σ * Real.exp (σ*l.cage x) * ∫ w,Beacon σ w ∂μ:=by
 let b:= blade n u σ * Real.exp (σ*l.cage x)
 have he (w:E4):trunk l u x w ≤ b * Beacon σ w:=trunk_bound u x w h
 have hm:= hi.const_mul b
 have hc:Integrable (trunk l u x) μ:= hm.mono' (by unfold trunk; fun_prop) (Eventually.of_forall (fun w=> (Real.norm_eq_abs _).trans_le ((abs_of_nonneg (trunk_nn ..)).trans_le (he _))))
 refine ⟨hc,(integral_mono hc hm (he)).trans_eq (integral_const_mul _ _)⟩

def fee (d n u:ℕ)(σ:ℝ):ℝ:= Fintype.card (Jet d) * blade n u σ
lemma fee_nn (d n u:ℕ)(he:0≤σ):0≤fee d n u σ:= by unfold fee; have h:=blade_nn n u he; positivity

/-- Literal same-packet witness for every polynomial moment; **linear** in analytic ticket;
sum over all jets and over every field tape. Can symmetrize first (breeze).
-/
theorem merchants (he:Sings l d h F B)(hp:Lyrics F)(hB:0≤B):
 ∃ μ ν:Tape n I→Jet d→Measure E4,Crew d σ F μ ν ∧ ∀ u:ℕ,(∀ x s, Integrable (trunk l u x) (μ x s)∧Integrable (trunk l u x) (ν x s)) ∧
 SumBudget (fun x=>tithe l u d μ x+tithe l u d ν x) (fee d n u σ * B):=by
 let e(x:Tape n I):= purse d h (F x)
 let p(x):=(e x).toReal
 have ht(x):e x≠⊤:=ne_top_of_le_ne_top ENNReal.ofReal_ne_top (he.plain x)
 have hf(x)(f):|F x f|≤p x* beam d h f:=by
   apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ENNReal.toReal_nonneg (beam_nn ..))).mp
   rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (ht x)]
   exact purse_gives _ _ (hp _) _
 choose μ ν hμ using fun x=>concert d h (sheet (hp x)) ENNReal.toReal_nonneg (hf x)
 refine ⟨μ,ν,⟨fun x s=>?_,fun x f=>(hμ x).2 f⟩,fun u=>?_⟩
 · obtain ⟨ha,hb,hc,hd,he1⟩:= (hμ x).1 s;exact ⟨ha,hb,hc,hd⟩
 let P:= tithe l (n:=n) u d
 let f(x):=P μ x+P ν x
 let b(x:Tape n I):=Real.exp (σ*l.cage x)
 let N:ℝ:= Fintype.card (Jet d)
 let C:=blade n u σ; have hC:0≤C:=blade_nn _ _ h.le
 have h'(x:Tape n I)(s:Jet d):Integrable (trunk l u x) (μ x s)∧Integrable (trunk l u x) (ν x s)∧
    (∫ w,trunk l u x w ∂μ x s)+(∫ w,trunk l u x w ∂ν x s)≤ C*b x*p x:=by
   obtain ⟨_,_,hy,hz,hj⟩:= (hμ x).1 s
   obtain ⟨ha,hc⟩:=dues (l:=l) hy u h x
   obtain ⟨hb,hd⟩:=dues (l:=l) hz u h x
   refine ⟨ha,hb,(add_le_add hc hd).trans ?_⟩; rw [← mul_add]; exact mul_le_mul_of_nonneg_left hj (mul_nonneg hC (Real.exp_pos _).le)
 have hnn(x):0≤f x:= by unfold f P tithe; exact add_nonneg (sum_nonneg (fun _ _=>integral_nonneg (fun w=>trunk_nn _ _))) (sum_nonneg (fun _ _=>integral_nonneg (fun w=>trunk_nn _ _)))
 have hv(x:Tape n I): f x ≤ fee d n u σ*(p x*b x):=by
   unfold f P tithe; rw [←sum_add_distrib]; apply (sum_le_sum (fun s _=> (h' x s).2.2)).trans_eq
   rw [sum_const,card_univ,nsmul_eq_mul];unfold fee C; ring
 have hk:= fee_nn d n u h.le
 have hd:(∑' x, ENNReal.ofReal (f x)) ≤ ENNReal.ofReal (fee d n u σ * B):=calc
  _ ≤ ∑' x,(ENNReal.ofReal (fee d n u σ) * gems l d h F x):= ENNReal.tsum_le_tsum fun x=> by
    apply (ENNReal.ofReal_le_ofReal (hv _)).trans_eq
    rw [ENNReal.ofReal_mul hk,ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (ht x)];rfl
  _ ≤ _:=by rw [ENNReal.tsum_mul_left,ENNReal.ofReal_mul hk];exact mul_le_mul_right he _
 have hs:= ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd)
 have HH:Summable f:= hs.congr fun x=>ENNReal.toReal_ofReal (hnn x)
 refine ⟨fun x s=>⟨(h' x s).1,(h' x s).2.1⟩,hnn,HH,?_⟩
 rw [← ENNReal.ofReal_tsum_of_nonneg hnn HH] at hd; exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hk hB)).mp hd
end YM.RG08.Jetty
