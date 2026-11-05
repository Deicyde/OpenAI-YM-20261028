import YM.TraceExtension.Perfect.Lunar
import YM.Planned.PRIMARY_INTEGRAL_295.Bijets

/-! # Basis names and approximation on smooth stencils, count in native real columns -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {c f:Side}{G:Gauge}

inductive RowGrade
| unit
| foot (i:Axis)
| paw (i j:Axis)
| watch
  deriving DecidableEq
namespace RowGrade
noncomputable instance : Fintype RowGrade:= Fintype.ofSurjective (f:=(Sum.elim (α:=Unit⊕Unit) (β:=Axis ⊕ (Axis×Axis)) (Sum.elim (fun _=>unit) (fun _=>watch)) (Sum.elim foot (Function.uncurry paw)))) (fun a=>by cases a with
   | unit=> exact ⟨.inl (.inl ()),rfl⟩
   | foot i=> exact ⟨.inr (.inl i),rfl⟩
   | paw i j=> exact ⟨.inr (.inr (i,j)),rfl⟩
   | watch=> exact ⟨.inl (.inr ()),rfl⟩)

def degree : RowGrade→ℕ | unit=>1 | foot _=>2 | paw _ _=>3 | watch=>3
def price : RowGrade→ Cover→ℝ
 | unit,_=>1
 | foot i,x=>(x i:ℝ)
 | paw i j,x=> ((x i:ℝ)+(x j:ℝ))^2
 | watch,_=>1

def violet (G:Gauge) := G
end RowGrade
abbrev Tit (G : Gauge) := RowGrade × (Loc G 1)
abbrev ScoreG (u : Tit G) := u.1.degree
abbrev Ox (n : Side) (i:pairA G n):= i.elim Prod.fst Prod.fst
def strollT (j: Tit G)(x:Site f)(i: Lines G f 1): ℝ:= if i.2=j.2 then j.1.price (lift (i.1-x)) else 0

def ballad (j:Tit G)(x:Site f) : Acr G f:= if j.1=.watch then Sum.elim 0 (strollT j x) else Sum.elim (strollT j x) 0
lemma ballad_mix (j:Tit G)(x:Site f)(h:j.1 ≠ .watch): (bite G f (ballad j x)).1=strollT j x ∧ (bite G f (ballad j x)).2=0 := by rw [ballad,if_neg h]; exact ⟨rfl,rfl⟩
lemma ballad_water (j:Tit G)(x:Site f)(h:j.1=.watch): (bite G f (ballad j x)).2=strollT j x ∧ (bite G f (ballad j x)).1=0 := by rw [ballad,if_pos h]; exact ⟨rfl,rfl⟩
lemma stroll_bound (j:Tit G)(x i): |strollT (f:=f) j x i|≤4*(1+(separation x i.1:ℝ))^2:=by
 unfold strollT; split
 next he => let r:=separation x i.1; let C:ℝ:=1+r; have ht:0 ≤ (r:ℝ):= Nat.cast_nonneg (α:=ℝ) _
            have h(i'): |(lift (i.1-x) i':ℝ)| ≤ r := (component_cost x i.1 i').trans_eq (congr_arg ((↑):ℕ→ℝ) (separation_comm ..))
            unfold RowGrade.price; split
            · simp; change _ ≤ 4*(1+(r:ℝ))^2; nlinarith
            · next a hq => change _ ≤ 4*(1+(r:ℝ))^2; apply (h a).trans; nlinarith
            · next a b hq=> rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; apply le_trans (pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le ..).trans (add_le_add (h a) (h b))) 2); change _≤4*(1+(r:ℝ))^2;nlinarith
            · simp; change _ ≤ 4*(1+(r:ℝ))^2;nlinarith
 simp; positivity
lemma ballad_bound (j:Tit G)(x:Site f)(i) : |ballad j x i| ≤ 4*(1+(landW x i :ℝ))^2:=by
 unfold ballad; split <;> cases i <;> first| exact stroll_bound ..| (change |(0:ℝ)| ≤ _; rw [abs_zero]; positivity)

-- filter tests. rolling positions. Funds may migrate along c because stamp lap.
variable {W : Type*}{F: Filter W} [F.NeBot] {n:W→Side}
structure Stoke (F:Filter W)(x:∀ w,Site (n w))(K:∀ w,Acr G (n w)→ℝ)(v:Tit G→ Tit G→ℝ) (z:ℕ):Prop where
    taste (u h: Tit G): ScoreG u+ ScoreG h ≤ z→ Tendsto (fun w=>iteratedFDeriv ℝ 2 (K w) 0 ![ballad u (x w),ballad h (x w)]) F (𝓝 (v u h))
section costs
variable {I:W→Type} [∀ i,Fintype (I i)] [∀ i, DecidableEq (I i)]
    (X:∀ i,I i→ℕ) {α:ℝ}
-- analytic convergence in polynomial moment pair tests
-- standard t≥4 and uniform? price uses compare ∥u∥∞.
def Modest (F:Filter W)(x:∀ i,Rays (I i)) (k:ℕ): Prop:=∃ C:ℝ,0 ≤ C∧∀ᶠ i in F,∀ j:I i, |x i j| ≤ C*(1+(X i j:ℝ))^k

structure Crossed (F:Filter W)(f g:∀ i,Rays (I i)) (k:ℕ): Prop where
    pays : Modest X F f k ∧ Modest X F g k
    near : ∀ n:ℕ,∀ ε:ℝ,0 < ε→∀ᶠ i in F,∀ j:I i, X i j ≤ n→ |f i j-g i j|≤ε
variable {X}
lemma measured_mono {Y:∀ w,Rays (I w)}{k k':ℕ}(h:Modest X F Y k)(hp:k ≤ k'): Modest X F Y k':=by
 obtain ⟨C,c,y⟩:=h; exact ⟨C,c,y.mono (fun i h j=> (h j).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by simp) hp) c))⟩
omit [F.NeBot] in
lemma modest_add {f g:∀ w,Rays (I w)}{k:ℕ}(h:Modest X F f k)(hp:Modest X F g k): Modest X F (fun w=> f w+g w) k :=by
 obtain ⟨C,c,h⟩:=h; obtain ⟨D,d,g'⟩:=hp
 refine ⟨C+D,by positivity,?_⟩; filter_upwards [h,g'] with w hw hh j; rw [Pi.add_apply,add_mul]; exact (abs_add_le ..).trans (add_le_add (hw _) (hh _))
omit [F.NeBot] in
lemma braid_test {f g:∀ w,Rays (I w)}{k:ℕ}(h:Modest X F f k)(hx:∀ᶠ w in F,f w=g w): Crossed X F f g k:=by
 refine ⟨⟨h,?_⟩,fun n e he=>?_⟩
 · obtain ⟨a,C,c⟩:=h; refine ⟨a,C,?_⟩; filter_upwards [hx,c] with w hh hv; rw [← hh]; exact hv
 filter_upwards [hx] with w hk i _; rw [hk,sub_self,abs_zero]; exact he.le


variable {v y h : ∀ w,Rays (I w)} {k t:ℕ}
omit [F.NeBot] in
lemma Crossed.eval {w' b:ℕ}(hp:Crossed X F v y w')(hy:Modest X F h b)(ht:w'+b ≤ t)
  (ha:0<α)(M:∀ w,(Rays (I w)) [×2]→L[ℝ] ℝ)(e:ℝ)(he:0 ≤ e)(hC:∀ᶠ w in F,cost (X w) α t 0 (bank (M w)) ≤ e)(p:Bool):
    Tendsto (fun w=> if p then M w ![h w, v w-y w] else M w ![v w-y w,h w]) F (𝓝 0):=by
 let k:=w'
 obtain ⟨C,c,y'⟩:=hp.pays.1;obtain ⟨D,d,hD⟩:=hp.pays.2;obtain ⟨Y',k',hh⟩:=hy
 let Y:=max Y' 1;have hY:0<Y:=lt_of_lt_of_le zero_lt_one (le_max_right ..)
 apply Metric.tendsto_nhds.mpr; intro ε hε
 let u:= ε/(e+1); have hu:0 < u:=div_pos hε (by positivity)
 let q:ℝ:= Real.log ((C+D)*Y/u)
 obtain ⟨n,hn⟩ : ∃ n: ℕ, (C+D)*Y/u ≤ Real.exp (α*n):= by
     have ht:= Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ha); exact (ht.eventually (eventually_ge_atTop _)).exists
 let H:=Y*((1+(n:ℝ))^b); have hH:0<H:=mul_pos hY (by positivity)
 filter_upwards [y',hD,hh,hp.near n _ (div_pos hu hH),hC] with w hv hx h' he' hi
 let V:=v w-y w; let T:Fin 2→Rays (I w):=if p then ![h w,V] else ![V,h w]
 have htB(bx: I w): |V bx|≤(C+D)*(1+(X w bx:ℝ))^k:=by rw [add_mul]; exact (abs_sub ..).trans (add_le_add (hv bx) (hx bx))
 have hh(j:Fin 2→I w)(i l:Fin 2): |V (j i)| * |h w (j l)| ≤ u*spot α t 0 (limitN (X w) j):=by
     let r:= limitN (X w) j
     have hk(t): (X w (j t):ℝ) ≤ r :=Nat.cast_le.mpr (limitN_ge ..)
     have hz:|V (j i)| *|h w (j l)| ≤ ((C+D)*Y)*(1+(r:ℝ))^t:=by
       have he : (1+(r:ℝ))^k*(1+(r:ℝ))^b≤(1+(r:ℝ))^t:=by rw [← pow_add]; exact pow_le_pow_right₀ (by simp) ht
       apply (mul_le_mul (htB (j i)) (h' (j l)) (abs_nonneg _) (by positivity)).trans
       refine le_trans ?_ (mul_le_mul_of_nonneg_left he (by positivity)); rw [show (C+D)*Y*((1+(r:ℝ))^k*(1+r)^b)= (C+D)*(1+(r:ℝ))^k*(Y*((1+r)^b)) from by ring]; unfold k; gcongr <;> first|exact limitN_ge ..|exact hk _|exact le_max_left ..
     by_cases hy : r<n
     · apply (mul_le_mul (b:=u/H) (d:=H) (he' _ ((limitN_ge (X w) _ i).trans hy.le)) ?_ (abs_nonneg _) (by positivity)).trans
       · rw [div_mul_cancel₀ u hH.ne']; exact le_mul_of_one_le_right hu.le (spot_one ha.le ..)
       apply (h' _).trans; unfold H; refine mul_le_mul (le_max_left ..) ?_ (by positivity) hY.le; exact pow_le_pow_left₀ (by positivity) (add_le_add_right (Nat.cast_le.mpr ((limitN_ge _ _ _).trans hy.le)) _) _
     apply hz.trans; have hG : (C+D)*Y ≤ u*Real.exp (α*r):=by
          rw [mul_comm u]; exact (div_le_iff₀ hu).mp (hn.trans (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (le_of_not_gt hy)) ha.le)))
     change (C+D)*Y*(1+(r:ℝ))^t≤u * spot α t 0 r; refine (mul_le_mul_of_nonneg_right hG (by positivity)).trans_eq ?_; simp [spot,shelter]; ring
 rw [dist_zero_right,show (if p then M w ![h w,v w-y w] else M w ![v w-y w,h w])=M w T from by unfold T V; split <;> rfl]; erw [many (.atomic 2) (M w) T]
 refine lt_of_le_of_lt ((norm_sum_le ..).trans ((Finset.sum_le_sum (s:=univ) (g:=fun j=> u*(spot α t 0 (limitN (X w) j)*‖bank (M w) j‖)) ?_).trans ?_)) (show u*e<ε by unfold u;field_simp; linarith only [hε])
 · intro i _; change ‖(∏ j:Fin 2,T j (i j)) • bank (M w) i‖≤_
   rw [norm_smul, Real.norm_eq_abs,Fin.prod_univ_two,abs_mul,← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); cases hp:p
   · unfold T; rw [hp]; exact hh i 0 1
   unfold T; rw [hp,mul_comm]; exact hh i 1 0
 rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hi hu.le

end costs
end YM.Trace.Perfect
