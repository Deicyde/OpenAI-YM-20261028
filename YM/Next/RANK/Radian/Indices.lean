import YM.Next.RANK.Hydro
import YM.Next.RANK.Radian.Close
import YM.Next.RANK.Tuning

/-!
# Maxwell derivative comparator

Usable with all lifts at norm≥1. Test after both stencils punched, down to
weighted operations of Prayer.gleam. Error from fixed damping (no limit). -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Filter Maxwell Topology Analysis Asymptotics Set Real Beamer Lattice Prayer VectorFourier
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace
local notation "𝑒" => Real.exp
local notation "ℑ" => Complex.I

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Gauge} {x : E4} {n : ℕ} {f g : E4→F}
lemma stroll (s : List Axis) (h : ContDiffAt ℝ ∞ f x) : ContDiffAt ℝ ∞ (dV s f) x:= by induction s generalizing f; exact h;rename_i a s ih; exact grad_smooth _ (ih h) (by simp)
lemma strolling (s : List Axis) (h : ∀ x∈Maxwell.away,ContDiffAt ℝ ∞ f x) (h' : ∀ x∈Maxwell.away,ContDiffAt ℝ ∞ g x) :
    EqOn (dV s (f-g)) (dV s f-dV s g) away:= by
  induction s with | nil=>exact fun _ _=>rfl| cons a s ih=>
  intro i hi
  apply Eq.trans (GermD (YM.basis a) (outside_eq _ _ ih hi)); unfold D
  rw [fderiv_sub ((stroll _ (h i hi)).differentiableAt (by simp)) ((stroll _ (h' i hi)).differentiableAt (by simp))];rfl
lemma crushed (s : List Axis) (h : f=ᶠ[𝓝 x] g) : dV s f=ᶠ[𝓝 x]dV s g := by induction s with
| nil=>exact h
| cons a s ih=>exact (show ∀ᶠ v in 𝓝 x, _ from (show fderiv ℝ (dV s f)=ᶠ[𝓝 x] fderiv ℝ (dV s g) from ih.fderiv)).mono fun i hi=> congr_arg (fun x:E4→L[ℝ] F=>x (YM.basis a)) hi
lemma echoes {f : E4→ℝ} (s : List Axis) (h : ∀ x∈away,ContDiffAt ℝ ∞ f x) : EqOn (dV s (fun x=>(↑(f x):ℂ))) (fun x=>(↑(dV s f x):ℂ)) away:= by
  induction s with | nil=>exact fun _ _=>rfl| cons a b ih=>
  intro x hx; apply Eq.trans (GermD (YM.basis a) (outside_eq _ _ ih hx))
  let A:= Complex.ofRealCLM
  change fderiv ℝ (A∘ dV b f) x (basis a) = A _; rw [fderiv_comp x (A.differentiableAt),A.fderiv]; rfl
  exact (stroll _ (h x hx)).differentiableAt (by simp)

lemma dVcoeff (n) (t : Fin n→ Axis) (hf : ∀ x∈ away,ContDiffAt ℝ ∞ f x) {x} (hx : x∈away) :
    dV (List.ofFn t).reverse f x=(↑n.factorial:ℝ) • (Tensor.coeff f n x (YM.basis ∘ t)):= by
  induction n generalizing f x with
  | zero=> simp [dV,Tensor.coeff]
  | succ n ih=>
    let u:= t 0; let s:= Fin.tail t
    have hm : ContDiffAt ℝ (↑(n+1:ℕ)) f x:= (hf _ hx).of_le (WithTop.coe_le_coe.mpr le_top)
    rw [show (basis ∘ t) = Fin.cons (basis u) (basis ∘ s) by funext i;cases i using Fin.cases<;>rfl,Tensor.coeff_apply_cons hm]
    rw [List.ofFn_succ,List.reverse_cons, dV,List.foldr_append];change dV (List.ofFn s).reverse (grad u f) x=_; rw [ih s (fun i hi=>grad_smooth _ (hf i hi) (by simp)) hx,smul_smul]; simp [grad,Nat.factorial_succ]
    congr 1; field_simp

-- h multiplier definition; singular point may be arbitrary for transform

def raypath (L K : Degree G) := (List.ofFn K.layout).reverse++(List.ofFn L.layout).reverse

def feather (i j a b : Axis) {F : Type*} [Zero F] [Sub F] (g : Axis→Axis→F) :=
    ((if a = j then g i b else 0) - (if b=j then g i a else 0)) -
      ((if a=i then g j b else 0) - (if b=i then g j a else 0))

def paints (L K : Degree G) (x : Axis→Axis→E4→ℂ) : E4→ℂ :=
    if L.paint=K.paint then ((-1:ℂ)^K.degree) • feather L.a.val.1 L.a.val.2 K.a.val.1 K.a.val.2 x else 0

def HeatP (b : ℝ) (L K : Degree G) : E4 →ℂ := paints L K fun i j=>press (raypath L K++[i,j]) (liturgy b)

lemma Moment.sealing (t : ℂ) {f : E4→ℂ} (h : Moment f) : Moment (t • f):= by
  refine ⟨h.integral.smul t,fun v=>?_⟩
  refine (Integrable.const_mul (h.price v) ‖t‖).congr (Eventually.of_forall ?_); intro i
  change ‖t‖*(_*_)=_ ;simp only [Pi.smul_apply,norm_smul]; ring
lemma Moment.assemble (L K : Degree G) (t : Axis→Axis→ E4→ℂ) (h : ∀ i j,Moment (t i j)):Moment (paints L K t):= by
  unfold paints; split;swap
  · exact Moment.zero
  apply Moment.sealing; apply Moment.sub (Moment.sub ?_ ?_) (Moment.sub ?_ ?_) <;> split <;> first|apply h|exact Moment.zero

lemma harmon_feather (L K : Degree G) (t : Axis→Axis→ E4→ℂ) (h : ∀ i j,Moment (t i j)) : harmon (paints L K t) = paints L K (fun i j=> harmon (t i j)):= by
  unfold paints;split_ifs with hp; swap; exact harmon_zero
  rw [harmon_scale]; refine congr_arg _ ?_; unfold feather
  have hi (_s i j u v : Axis): Moment (if u=v then t i j else 0):= by split;exact h _ _;exact Moment.zero
  have H (u v _c i j : Axis): harmon (if i=j then t u v else 0)=(if i=j then harmon (t u v) else 0):=by split;rfl; exact harmon_zero
  let i:=L.a.val.1
  apply (harmon_sub ((Moment.sub (hi i _ _ _ _) (hi i _ _ _ _)).integral) ((Moment.sub (hi i _ _ _ _) (hi i _ _ _ _)).integral)).trans
  rw [harmon_sub (hi i _ _ _ _).integral (hi i _ _ _ _).integral,harmon_sub (hi i _ _ _ _).integral (hi i _ _ _ _).integral]; simp_rw [H _ _ i]

lemma sparse_heat (i j a b : Axis) (f : Axis→Axis→E4→ℂ) {B : ℝ} (z : E4) (h : ∀ i j, ‖f i j z‖ ≤ B): ‖feather i j a b f z‖ ≤ 4*B:= by
  have he (c d i j k : Axis) : ‖(if c=d then f i j else (0:E4→ℂ)) z‖ ≤ B:=by split_ifs;exact h _ _;exact (norm_zero (E:=ℂ)).le.trans ((norm_nonneg _).trans (h k k))
  unfold feather; simp only [Pi.sub_apply]; apply (norm_sub_le ..).trans; apply le_trans (add_le_add (norm_sub_le ..) (norm_sub_le ..)); linarith [he a j i b i,he b j i a i,he a i j b i,he b i j a i]
lemma cancel_colour (L K : Degree G) (t q : Axis→Axis→E4→ℂ) : paints L K (t-q) = paints L K t-paints L K q:= by
  unfold paints;split;swap; simp
  rw [← smul_sub]; apply congr_arg _; unfold feather; simp only [Pi.sub_apply];split_ifs <;> abel
lemma colour_touch (L K : Degree G) (t p : Axis→Axis→ E4→ℂ) {z : E4} (h : ∀ i j,t i j z=p i j z) : paints L K t z=paints L K p z :=by unfold paints feather;split<;>simp only [Pi.smul_apply, Pi.sub_apply];split_ifs<;>simp [h]

-- leading exact normalization leg convention
lemma contact (L K : Degree G) (x : E4) (hx:x≠0): paints L K (fun i j y=> (↑(dV (raypath L K++[i,j]) Maxwell.Green y):ℂ)) x=(Prayer.gleam L K x:ℂ):= by
  unfold paints; split
  · rename_i H; let i:= L.a.val.1;let j:=L.a.val.2;let a:=K.a.val.1;let b:=K.a.val.2
    let P := fun i j=> dV [i,j] Maxwell.Green
    let T:= feather i j a b P
    have he : EqOn T (Maxwell.bareCurl i j a b) away:= by
      intro v hv; simp only [T,feather,bareCurl,Pi.sub_apply,Bare.opp_grad hv]; split_ifs<;>rfl
    let u:=raypath L K
    let D i j:=dV u (P i j)
    have hz i j y: dV (raypath L K++[i,j]) Green y=D i j y:= by rw [dV,List.foldr_append];rfl
    have hp:dV u T x=feather i j a b D x:= by
      let F(s t x y:Axis) := if x=y then P s t else 0
      have H (x y p q : Axis) : dV u (F x y p q) = if p=q then D x y else 0:=by unfold F;split;rfl; exact d_zero u
      have hx' : x∈away:= hx
      have hy i j p q z (h : z∈away): ContDiffAt ℝ ∞ (F i j p q) z:= by unfold F;split;exact stroll [_,_] (Maxwell.freeSmooth h); exact contDiffAt_const
      change dV u ((F i b a j- F i a b j)-(F j b a i-F j a b i)) x=_
      rw [strolling u (f:=F i b a j- F i a b j) (g:=F j b a i - F j a b i) (fun z h=>(hy i b _ _ z h).sub (hy i a _ _ z h)) (fun z h=>(hy j b _ _ z h).sub (hy j a _ _ z h)) hx']
      simp only [Pi.sub_apply]; rw [strolling u (hy i b _ _) (hy i a _ _) hx',strolling u (hy j b _ _) (hy j a _ _) hx']; simp only [Pi.sub_apply,H]; rfl
    let X:=bareCurl i j a b; let X' z:=Tensor.coeff X L.degree z (basis ∘ L.layout);let r : ℝ:= L.degree.factorial
    let q:ℝ:=K.degree.factorial
    have hv : feather i j a b (fun i j y=>(↑(D i j y):ℂ)) x = (↑(dV u X x):ℂ):= by
      rw [← (crushed u (outside_eq T X he hx)).eq_of_nhds,hp]; unfold feather;split_ifs <;> simp [*]
    simp_rw [hz]; change ((-1:ℂ)^K.degree) • feather i j a b (fun i j y=>(↑(D i j y):ℂ)) x= _; rw [hv]
    have hx' z(h:z∈away): ContDiffAt ℝ ∞ X z:= Bare.curl_diff h _ _ _ _
    have he:dV u X x=q*(r*(Tensor.coeff X' K.degree x (basis∘K.layout))):= by
      let s:=(List.ofFn K.layout).reverse;let p:=(List.ofFn L.layout).reverse
      unfold dV u raypath; rw [List.foldr_append]; change dV s (dV p X) x = _
      have h:dV p X =ᶠ[𝓝 x] r • X':= outside_eq _ _ (fun z hz=> dVcoeff L.degree _ hx' hz) hx
      have hp z (h:z∈away):ContDiffAt ℝ ∞ X' z:= (ContinuousMultilinearMap.apply ℝ _ ℝ (basis ∘ L.layout)).contDiff.contDiffAt.comp z (Tensor.coeff_smooth (hx' z h) _)
      rw [(crushed s h).eq_of_nhds,dVcoeff _ K.layout (f:=r • X') (fun z h=>(hp z h).const_smul r) hx,Tensor.coeff_smul r ((hp _ hx).of_le (WithTop.coe_le_coe.mpr le_top))]; rfl
    rw [he,gleam,if_pos H]; simp only [smul_eq_mul]; unfold r q X' X i j a b;push_cast;ring
  rename_i H; rw [gleam,if_neg H,mul_zero,Complex.ofReal_zero]; rfl
where
 d_zero (s : List Axis):dV s (0:E4→ℝ)=0:= by induction s with | nil=>rfl| cons a l I=> change grad a (dV l _) = _; rw [I];ext;simp [grad,D]
end YM.Next.Rank.Radian
namespace YM.Next.Rank.Radian
open MeasureTheory Filter Maxwell Topology Analysis Asymptotics Set Real Beamer Lattice Prayer VectorFourier Finset
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace
variable {G : Gauge}
lemma heat_perturbed (a b : Degree G) {t : ℝ} (h : 0<t) (k : ℕ) : ∃ C : ℝ, 0≤ C∧∀x:E4, 1≤‖x‖→ ‖harmon (HeatP t a b) x-(Prayer.gleam a b x:ℂ)‖ ≤ C/‖x‖^k:= by
  let s:= π^2/t; have hs : 0 < s:= div_pos (pow_pos Real.pi_pos _) h
  let d (f:E4→ℝ) i j:= dV (raypath a b++[i,j]) f
  let U := Green * blaze s
  have hr:Spire Green:= Spire.product (.rope normal) .hill
  choose C hc hC using fun i j=>faded hr hs (raypath a b++[i,j]) k
  let c : ℝ:= ∑ i,∑ j,C i j; have he i j : C i j ≤ c:= (single_le_sum (fun j _=> hc i j) (mem_univ j)).trans (single_le_sum (fun i _=>sum_nonneg fun j _=>hc i j) (mem_univ i))
  have hh:0 ≤ c:=le_trans (hc 0 0) (he _ _)
  refine ⟨4*c,by positivity,fun z hz=>?_⟩
  have hp:0<‖z‖:= zero_lt_one.trans_le hz
  have hg:z ∈ away:=norm_pos_iff.mp hp
  have hT i j : ‖d U i j z‖ ≤ c/‖z‖^k:= (le_div_iff₀ (pow_pos hp k)).2 (le_trans (b:=C i j) ((mul_comm ..).trans_le (hC _ _ _ hz)) (he _ _))
  have hH : ∀ y∈away,ContDiffAt ℝ ∞ U y:= fun y hy=> (freeSmooth hy).mul (Real.contDiff_exp.contDiffAt.comp _ (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt))
  have hx : harmon (liturgy t)=ᶠ[𝓝 z] fun y=>(↑((Green-U) y):ℂ):= outside_eq _ _ (fun y hy=> by rw [chants_h h y hy]; apply congr_arg; unfold U s; simp only [Pi.sub_apply,Pi.mul_apply,blaze,mul_sub,mul_one]; ring_nf) hg
  let A:=fun i j (z : E4)=> (↑(d Green i j z):ℂ); let D:=fun i j z=> (↑(d U i j z):ℂ)
  have hy l g:dV (raypath a b++[l,g]) (harmon (liturgy t)) z=(A-D) l g z:= by
    rw [(crushed _ hx).eq_of_nhds,echoes _ (f:=Green-U) (fun y hy=>(freeSmooth hy).sub (hH y hy)) hg]; dsimp only; rw [strolling _ (fun _ h=>Maxwell.freeSmooth h) hH hg]; simp only [Pi.sub_apply, Complex.ofReal_sub];rfl
  have ht: harmon (HeatP t a b) z = paints a b (A-D) z:= by
    rw [HeatP,harmon_feather a b _ (fun i j=> Moment.pressed _ (passion h))]
    apply colour_touch; intro i j; rw [takes _ (passion h)];exact hy _ _
  rw [ht,cancel_colour, Pi.sub_apply,← contact _ _ _ hg]; change ‖paints a b A z-_ - paints a b A z‖≤ _; rw [sub_sub_cancel_left,norm_neg]
  unfold paints; split
  · rw [Pi.smul_apply,norm_smul]; simp only [norm_pow,norm_neg,norm_one, one_pow, one_mul]; refine le_trans (sparse_heat _ _ _ _ _ _ (fun i j=>?_)) (le_of_eq (mul_div_assoc ..).symm)
    unfold D;rw [Complex.norm_real]; exact hT ..
  change ‖(0:ℂ)‖≤_;rw [norm_zero]; positivity
end YM.Next.Rank.Radian
