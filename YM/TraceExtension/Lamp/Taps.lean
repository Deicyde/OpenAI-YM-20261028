import YM.TraceExtension.Lamp.Keg

/-!
# Aperture finite taps (no ties to top of regulator mass).

Keep contracted momentum contour unselected and REAL integral at 0.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r l:ℕ}{α σ μ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{L:Filter W}
-- 1-2 degree taps exact Taylor along one contour
private def lum(f:ℤ→ℂ):=(1/2:ℂ)*(f 1-2*f 0+f (-1))
private def ace(f:ℤ→ℂ):=(1/12:ℂ)*(8*(f 1-f (-1))- (f 2-f (-2)))
def PanZ : (ℤ→ℂ)→ₗ[ℂ]ℂ:={
  toFun:=lum
  map_add':=fun f g=>by simp only[lum,Pi.add_apply];ring
  map_smul':=fun c f=>by simp only[lum,Pi.smul_apply, RingHom.id_apply,smul_eq_mul]; ring }
def FlopZ : (ℤ→ℂ)→ₗ[ℂ]ℂ:={
  toFun:=ace
  map_add':=fun f g=>by simp only[ace,Pi.add_apply];ring
  map_smul':=fun c f=>by simp only[ace,Pi.smul_apply, RingHom.id_apply,smul_eq_mul]; ring }
-- explicit
lemma pani (f:ℤ→ℂ) : PanZ f= (1/2:ℂ)*(f 1-2*f 0+f (-1)):=rfl
lemma flopi (f:ℤ→ℂ) : FlopZ f=(1/12:ℂ)*(8*(f 1-f (-1))-(f 2-f (-2))):=rfl
abbrev Dish:=ℤ × ℤ
def DishL (f:Dish→ℂ) :ℂ:= Complex.I *PanZ (fun w:ℤ=> FlopZ fun y=> f (w,y))
def Deb : (Dish→ℂ)→ₗ[ℂ]ℂ:={
  toFun:=DishL
  map_add':=fun f g=>by simp only[DishL,pani,flopi,Pi.add_apply];ring
  map_smul':=fun c f=>by simp only[DishL,pani,flopi,Pi.smul_apply,smul_eq_mul,RingHom.id_apply];ring }
lemma pan_coeff (i:ℕ)(v:ℂ)(h:i≤2): PanZ (fun a:ℤ=>(a:ℂ)^i * v)= if i=2 then v else 0:=by interval_cases i<;> rw [pani] <;> norm_num <;> ring
lemma flop_coeff (i:ℕ)(v:ℂ)(h:i≤3): FlopZ (fun a:ℤ=>(a:ℂ)^i*v)=if i=1 then v else 0:=by interval_cases i<;>rw[flopi] <;>norm_num <;> ring
lemma pan_coh {F H: W→ℤ→ℂ}(h:∀ i, Rose L (fun w=> F w i) (fun w=>H w i)) : Rose L (PanZ ∘ F) (PanZ ∘ H):=by
    exact roseRate (1/2:ℂ) (Rose.inc (Rose.dec (h 1) (roseRate 2 (h 0))) (h (-1)))
lemma disk_coh {F H: W→ Dish→ℂ}(h:∀ i,Rose L (fun w=> F w i) (fun w=>H w i)) : Rose L (Deb ∘ F) (Deb ∘ H):=by
    apply roseRate Complex.I (f:=fun w=> PanZ (fun x=> FlopZ fun y=> F w (x,y))) (g:=fun w=>PanZ (fun x=>FlopZ fun y=>H w (x,y)))
    refine pan_coh (F:=fun w x=> FlopZ fun y=> F w (x,y)) (H:= fun w x=> FlopZ fun y=>H w (x,y)) ?_
    intro i; have he(j:ℤ):= h (i,j)
    exact roseRate (1/12:ℂ) (Rose.dec (roseRate (8:ℂ) (Rose.dec (he 1) (he (-1)))) (Rose.dec (he 2) (he (-2))))
def flee (X Y: Track)(v:Dish): TresF (Fin 2):= ![(v.1:ℝ) • X,-((v.1:ℝ) • X)+(v.2:ℝ) • Y]
lemma flee_run (X Y:Track)(v:Dish): flee X Y v=(v.1:ℝ) • ![X,-X]+(v.2:ℝ) • ![0,Y]:=by ext1 i;fin_cases i; simp only [flee,Pi.add_apply,Pi.smul_apply]; simp; simp [flee]
lemma feeLow (x y z:X)(F:X→ℂ)(k:ℕ)(h:k<3)(p:ℤ) : FlopZ (fun i:ℤ=>neap k F z ((p:ℝ) • x+(i:ℝ) • y))=match k with
    | 0=>0
    | 1=> fderiv ℝ F z y
    | _=> (1/2:ℂ)*(p:ℂ)*(fderiv ℝ (fderiv ℝ F) z x y + fderiv ℝ (fderiv ℝ F) z y x):=by
    rw [flopi]
    interval_cases k
    · simp [neap0]
    · simp only [neap1, map_add,map_smul,Complex.real_smul]; push_cast; ring
    · simp only[neap2, map_add,map_smul, ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,Complex.real_smul]; push_cast; ring
lemma neap_low (x y z:X)(F:X→ℂ)(k:ℕ)(h:k<3) : Deb (fun a:Dish=>neap k F z ((a.1:ℝ) • x+(a.2:ℝ) • y))=0:=by
    change Complex.I* PanZ (fun p:ℤ=> FlopZ (fun q:ℤ=> neap k F z ((p:ℝ) • x + (q:ℝ) • y)))=0; simp_rw [feeLow x y z F k h]; rw[pani]; interval_cases k<;> norm_num <;> ring
variable {t:W→ℝ}
lemma rite (h:Wilt L t)(F: W →ℝ→ℂ)(m:ℕ)(hp:Honor F (m+1)):
    Rose L (fun i=> (t i:ℂ)⁻¹^m * F i (t i)) (fun i=> (t i:ℂ)⁻¹^m * (∑ k∈range (m+1), (t i:ℂ)^k * neap k (F i) 0 1)):=by
    obtain ⟨C,hC,H⟩:=hp.top
    let f(w):ℝ:= C*t w/m.factorial
    let X:=fun i=> F i (t i); let Y:=fun i=> (∑ k∈range (m+1), (t i:ℂ)^k * neap k (F i) 0 1)
    apply squeeze_zero_norm' ?_ (show Tendsto f L (𝓝 0) from by unfold f; simpa using (h.void.const_mul C).div_const (m.factorial:ℝ))
    refine Eventually.of_forall fun i=> ?_
    have hp':=h.pos i; have hv:= warm (F i) _ hp' (t i) ⟨hp'.le,le_rfl⟩ m (fun _ _=>H i _)
    simp only [Complex.real_smul, Complex.ofReal_pow] at hv
    change ‖(t i:ℂ)⁻¹^m*X i-(t i:ℂ)⁻¹^m*Y i‖ ≤ _
    rw[← mul_sub, norm_mul, norm_pow,norm_inv,Complex.norm_real, Real.norm_of_nonneg hp'.le]
    apply (mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq; unfold f; rw [pow_succ, inv_pow]; field_simp
lemma brief (h:Wilt L t)(F:W→ X→ℂ)(p:X)(m:ℕ)(hp:Honor F (m+1)):
    Rose L (fun i=> (t i:ℂ)⁻¹ ^m * F i (t i • p)) (fun i=> (t i:ℂ)⁻¹^m *∑ k∈range (m+1), (t i:ℂ)^k * neap k (F i) 0 p):=by
    let M:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) p
    let f(w):=F w∘ M; have he:= hp.dam M; apply (rite h f m he).chain
    obtain ⟨C,hC,H⟩:=hp.top; refine Rose.skip (Eventually.of_forall fun x=> ?_); have hv i:neap i (f x) 0 1=neap i (F x) 0 p:=by
       have he:=chord_n (0:X) p i (H x 0|>.analytic); rw[show (fun s:ℝ=> F x (0+s • p))= f x from funext fun s=>by simp only[zero_add]; rfl] at he;exact he
    dsimp only; simp_rw[hv]
lemma pan_brief (h:Wilt L t)(F:W→ X→ℂ)(p:X)(hp:Honor F 3):
    Rose L (fun i=> PanZ (fun k:ℤ=> ((t i:ℂ)⁻¹^ (2:ℕ))* F i (t i • ((k:ℝ) • p)))) (fun i=> neap 2 (F i) 0 p):=by
    let X(k:ℤ)(x:W):=(t x:ℂ)⁻¹^(2:ℕ)*∑ i∈Finset.range (2+1),(t x:ℂ)^i*neap i (F x) 0 ((k:ℝ) • p);
    apply (pan_coh (F:=fun i k=>_ ) (H:=fun i k=>X k i) (fun k => brief h F ((k:ℝ) • p) 2 hp)).chain; apply Rose.skip (Eventually.of_forall (fun i=>?_));rw [Function.comp_apply]; unfold X; simp only [pani, Finset.sum_range_succ,neap_tide,Complex.real_smul]; push_cast; simp only[sum_range_zero,zero_add,zero_pow (by decide:1≠0),zero_pow (by decide:1+1≠0)]; have hx : (t i:ℂ)≠0:=by exact_mod_cast (h.pos i).ne'
    field_simp; ring
lemma disk_brief (h:Wilt L t)(F: W→ X→ℂ)(x y:X)(hp:Honor F 4):
    let A(v:Dish) := (v.1:ℝ) • x+(v.2:ℝ) • y
    Rose L (fun i=> Deb (fun a:Dish=> (t i:ℂ)⁻¹ ^ (3:ℕ) * F i (t i • A a))) (fun i=> Deb fun a=> neap 3 (F i) 0 (A a)):=by
    intro A
    let Z(w)(i)(z:Dish) := (t w:ℂ)^i *neap i (F w) 0 (A z)
    have hv :=disk_coh (F:=fun i a=> (t i:ℂ)⁻¹ ^ (3:ℕ)*F i (t i • A a)) (H:=fun i a=> (t i:ℂ)⁻¹ ^ (3:ℕ)*∑ k∈range (3+1), Z i k a) (fun a=> brief h F (A a) 3 hp)
    apply hv.chain; apply Rose.skip (Eventually.of_forall fun i=>?_)
    change Deb _=_; dsimp only; rw [show (fun a=> (t i:ℂ)⁻¹ ^ (3:ℕ)*∑ k∈range (3+1),Z i k a)=(t i:ℂ)⁻¹^(3:ℕ) • ∑ k∈range (3+1),Z i k from by ext1 v; rw[Pi.smul_apply,Finset.sum_apply];rfl,map_smul,map_sum]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,zero_add]; unfold Z; simp only[show ∀ j:ℕ,(fun a=> (t i:ℂ)^j*neap j (F i) 0 (A a))= _ from fun j=> (rfl:_= (t i:ℂ)^j • fun a=> neap j (F i) 0 (A a)), map_smul];
    have hx : (t i:ℂ)≠0:=by exact_mod_cast (h.pos i).ne'
    rw[neap_low x y _ _ _ (by omega), neap_low x y _ _ _ (by omega), neap_low x y _ _ _ (by omega)]; simp[hx]
end YM.Trace.Lamp
