import YM.TraceExtension.Lamp.Tan
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{k m n r l:ℕ}{α σ a b c τ A C D:ℝ}
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]
abbrev WickL (G:Gauge):= Loc G 1→Loc G 1→Track×Track→ℂ
variable {W:Type*}{g:W→Side}{H K:WickL G}{T:Reed G}{L:Filter W}(d i b a:Axis)(q j:G.ColorIndex)
def song (K:WickL G)(T:Reed G)(a:Loc G 1)(z:Dish):=
   let p:=reel (ra d z.1); let x:=reel (reab d b z); let y:=mood G i q
   T a y x * K a y (p,x)+T a y p *K a y (x,p)
lemma tune_select (h: d≠i)(he:Campus T)(hp:Kelly K)(z:Dish):
   let s:ℤ:=z.1; let t:ℤ:= z.2
   let P:Track:= (s:ℝ) • step d
   let Q:Track:= -(s:ℝ) • step d + (t:ℝ) •step b
   let X:= K (mood G a j) (mood G i q)
   song d i b q K T (mood G a j) z=tickt T j q *(MaxwellK Q a i * ((s:ℂ)*X (step d,0))+
     MaxwellK P a i *(- (s:ℂ) *X (step d,0)+(t:ℂ)*X (step b,0))):=by
    intro s t P Q X
    have hx:P=reel (ra d z.1):=by rw[ra,reel_z,reel_i]
    have hh:Q=reel (reab d b z):=by rw[reab,reel_be,reel_neg,reel_z,reel_z,reel_i,reel_i];simp [Q,s,t]
    have he'(d b:Axis)(x y:ℝ): T (mood G a j) (mood G i q) (x • step d+y • step b)= _ := he.full a i d b j q x y
    have hv:T (mood G a j) (mood G i q) P=tickt T j q*MaxwellK P a i:=by simpa only[zero_smul,add_zero] using he' d d (s:ℝ) 0
    have hK:X (P,0)=(s:ℂ)*X (step d,0):=by unfold X P; rw[hp.scale];push_cast;rfl
    have hL:X (Q,0)= -(s:ℂ)*X (step d,0)+(t:ℂ)*X (step b,0):=by unfold X Q; rw[hp.plus,hp.scale,hp.scale];push_cast;rfl
    dsimp only[song]; rw [hp.rear,hp.rear, ← hx, ←hh,hv, show T (mood G a j) (mood G i q) Q = _ from he' d b (-(s:ℝ)) (t:ℝ)]; change (_ *X (P,_)+_*X (Q,_))=_; rw [hK,hL]; unfold Q; ring
lemma song_bill (h:d≠i) (he:Campus T)(hp:Kelly K): let X:=K (mood G a j) (mood G i q); let u:=X (step d,0); let v:= X (step b,0);
    Deb (song d i b q K T (mood G a j))= Complex.I*tickt T j q *((if b=d ∧ a=i then -2*u else 0)+(if a=d ∧ b=i then u else 0)+(if a=i then v else 0)):=by
    intro X u v
    let F(w:Dish):= MaxwellK (-(w.1:ℝ) •step d+(w.2:ℝ) • step b) a i
    let c(w:Dish):=(w.1:ℂ); let l(w:Dish):=(w.2:ℂ)
    let y(w:Dish):=F w*(c w*u)+(if a=i then c w ^(2:ℕ) else 0)*(-c w*u+l w*v)
    have ht:song d i b q K T (mood G a j)= tickt T j q • y:=funext (fun w=>by
       rw[tune_select _ _ _ _ _ _ h he hp,max_one_i,Pi.smul_apply]; by_cases hx:a=i
       · have hz : a=i∧a≠d:=⟨hx,hx.symm ▸ h.symm⟩; rw[if_pos hz]; unfold y; rw[if_pos hx]; push_cast;rfl
       rw[if_neg (fun hb=>hx hb.1)]; unfold y; rw [if_neg hx]; rfl)
    rw [ht, map_smul, smul_eq_mul]
    have hz: Deb y=Complex.I*((if b=d∧a=i then -2*u else 0)+(if a=d∧ b=i then u else 0)+(if a=i then v else 0)):=by
       change Complex.I*PanZ (fun w=>FlopZ fun t=> y (w,t))= _; rw[pani]; simp only[flopi]; unfold y F c l
       by_cases hv:b=d
       · subst b; simp only[← add_smul,max_one_i]; by_cases hb:a=i<;> subst_vars <;> simp [*, Ne.symm h]; ring
       simp_rw[maxdi _ _ _ _ (Ne.symm hv)]; push_cast; by_cases ha:a=i
       · subst a; by_cases hp':b=i<;> simp[hp',h,h.symm,hv] <;> ring
       by_cases hi:b=i
       · subst b; by_cases hf:a=d<;> simp [ha,h,h.symm,hf]<;> ring
       simp [hv,ha,h,h.symm,hi,Ne.symm hi]
    rw[hz]; ring
variable {P:Axis→ WickL G}
lemma tune_axis (h:d≠i)(he:Campus T)(hp:Kelly K) : (∑ a:Axis,Deb (song d i b q K T (coord a,j)))=
    Complex.I*tickt T j q * (-2*(if b=d then K (coord i,j) (mood G i q) (step d,0) else 0)+(if b=i then K (mood G d j) (mood G i q) (step d,0) else 0)+ K (coord i,j) (coord i,q) (step b,0)):=by
    simp_rw [show ∀ a:Axis,Deb (song d i b q K T (coord a,j))=_ from fun a=> song_bill d i b a q j h he hp, ← mul_sum]; by_cases hx:b=d<;>by_cases hy:b=i<;> simp [sum_add_distrib,hx,hy,mood,Ne.symm h,h]
lemma tune_body (h:d≠i)(he:Campus T)(hp:∀ b,Kelly (P b)):
    ∑ b:Axis, (∑ a:Axis,Deb (song d i b q (P b) T (coord a,j)))=
    Complex.I*tickt T j q * ( -2*P d (coord i,j) (coord i,q) (step d,0)+ P i (coord d,j) (coord i,q) (step d,0)+ ∑ b:Axis, P b (coord i,j) (coord i,q) (step b,0)):=by
    simp_rw[tune_axis d i _ q j h he (hp _)]; rw [← mul_sum]; simp only[Finset.sum_add_distrib]; simp [mul_ite,mood]
lemma turn_tank (he:Campus T)(hp:∀ b,Kelly (P b)):
    ∑ d:Axis,∑ i:Axis,(if d=i then 0 else ∑ b:Axis,∑ a:Axis,Deb (song d i b q (P b) T (coord a,j)))=0:=by
    let X(d i b:Axis):=P b (coord i,j) (coord i,q) (step d,0)
    have hZ(d i:Axis): P i (coord d,j) (coord i,q) (step d,0) = -X i d i:= (hp i).inverse _ _ _ _
    have hv(i:Axis): X i i i=0:=by have he:=hZ i i; change X i i i=-X i i i at he; linear_combination he/2
    have ht(i:Axis): ∑ d:Axis, (if d=i then 0 else ∑ b:Axis,X b i b)=3*∑ b,X b i b:=by fin_cases i<;>simp [Fin.sum_univ_four]<;> ring
    let F(d i):= if d=i then 0 else ∑ b:Axis,∑ a:Axis,Deb (song d i b q (P b) T (coord a,j)); let Λ:=Complex.I*tickt T j q
    have hF(d i:Axis): F d i= Λ*(-2* X d i d-(if d=i then 0 else X i d i)+(if d=i then 0 else ∑ b:Axis,X b i b)):=by
        unfold F; split_ifs with hh; · subst d;rw[hv]; ring
        rw [tune_body d i q j hh he hp,hZ]; rfl
    change ∑ d:Axis,∑ i:Axis,F d i=0; simp_rw[hF,← Finset.mul_sum,sum_add_distrib, Finset.sum_sub_distrib]; simp [Fin.sum_univ_four,hv]; right; ring
end YM.Trace.Lamp
