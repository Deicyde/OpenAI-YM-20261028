import YM.Next.RANK.Radian.Means
import YM.Next.RANK.Radian.TK

/-! Pair difference symbol operations and low-order stamp verification. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric Beamer Lattice Prayer Finset
open Atlas Normal Perch Wall CellsInt Function
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace
local notation "ℑ" => Complex.I

variable {E : Type*} {n j d : ℕ} {f g h q : E4→ℂ} {b A : ℝ} {H : Gauge}

def origin (L : Degree H) : Degree H:= ⟨L.a,L.paint,0,0,Fin.elim0⟩

-- use arbitrary lists of directions (not necessarily symmetric in use)

def chimes (w x : E4) : ℂ := 2* (π:ℂ) * ℑ * inner ℝ x w
def peck (v : List E4): E4→ℂ := (v.map chimes).prod
def readD (v : E4) := wave v - 1
def staccato (v : List E4): E4→ℂ := (v.map readD).prod

-- analytic jets at zero
lemma glides (v : E4) : ContDiff ℝ ∞ (chimes v):= by unfold chimes; apply ContDiff.mul contDiff_const; exact Complex.ofRealCLM.contDiff.comp (show ContDiff ℝ ∞ (fun x=>inner ℝ x v) from ContDiff.inner ℝ (contDiff_id (𝕜:=ℝ)) contDiff_const)
lemma terrel (v : E4) (x : E4) : wave v x=Complex.exp (chimes v x):= by
  rw [wave,Real.fourierChar_apply]; unfold chimes; push_cast; rw [inner_neg_right,Complex.ofReal_neg]; congr 1;ring
lemma tune (v : E4) : ContDiff ℝ ∞ (readD v):= by unfold readD; rw [show wave v=(fun x=> Complex.exp (chimes v x)) from funext (terrel v)]; exact (glides v).cexp.sub contDiff_const
lemma trill (v): (chimes v) 0=0:= by simp [chimes]
lemma teleports (v) : readD v 0=0:= by rw [readD,Pi.sub_apply,terrel,trill,Complex.exp_zero];exact sub_self _
lemma transonic (v : E4) : fderiv ℝ (readD v-chimes v) 0=0:= by
  rw [fderiv_sub ((tune v).differentiable (by simp) _) ((glides v).differentiable (by simp) _)]
  have he:readD v=(fun x=> Complex.exp (chimes v x))-fun _ : E4=>1:= by ext1 i; unfold readD; rw [Pi.sub_apply,terrel];rfl
  have ht := ((((glides v).differentiable (by simp) 0).hasFDerivAt).cexp).sub (hasFDerivAt_const (𝕜:=ℝ) (1:ℂ) (0:E4))
  rw [he, ht.fderiv,trill, Complex.exp_zero,one_smul,sub_zero,sub_self]
lemma chore (v) : chimes (basis v)=chirp v:= by funext x; unfold chirp chimes;rw [real_inner_comm,basis_inner]
lemma bore (x : List Axis) (F) : press x F=peck (x.map basis)*F:= by
  induction x with
  | nil=>rw [press, peck];simp
  | cons a t IH=> unfold peck; simp_rw [List.map_cons,List.prod_cons]; change crank a (press t F)=(chimes (YM.basis a) * peck _)*F; rw [IH, crank,chore,mul_assoc]
lemma playlist (t : Fin n→Axis) : peck ((List.ofFn ((fun i : Axis => -YM.basis i) ∘ t)))=((-1:ℂ)^n) • peck (List.ofFn (YM.basis∘ t)):=by
  induction n with
  | zero=> simp
  | succ n IH=>
    let i:=t 0; let v:= Fin.tail t
    rw [List.ofFn_succ,List.ofFn_succ]; change chimes (-basis i) * peck (List.ofFn ((-basis) ∘ v)) = _ • (chimes (basis i) * peck (List.ofFn (basis ∘ v)))
    rw [show peck (List.ofFn ((-basis) ∘ v))= _ from IH (Fin.tail t) ];
    have hp(x): chimes (-basis i) x= -chimes (basis i) x := by simp [chimes]
    ext1 x; simp only [Pi.mul_apply,hp,Pi.smul_apply, smul_eq_mul]; rw [pow_succ]; ring

lemma reversal (l : List E4) : peck l.reverse=peck l:= by simp only [peck,List.map_reverse,List.prod_reverse]
lemma wing (L K : Degree H) :
    let H':=(List.ofFn L.layout).map YM.basis
    let T:=(List.ofFn K.layout).map fun i=> -YM.basis i
    peck (H'++ T)=((-1:ℂ)^K.degree) • peck ((raypath L K).map basis):= by
  intro H' T; rw [raypath,List.map_append]
  have he (x y : List E4) : peck (x++y)=peck x*peck y:= by simp only [peck,List.map_append,List.prod_append]
  rw [he,he,List.map_reverse,List.map_reverse,reversal,reversal]; unfold H' T; simp only [List.map_ofFn]; rw [playlist (n:=K.degree) K.layout]
  simp only [mul_smul_comm,mul_comm]

def reel (A B : Degree H):= ((List.ofFn A.layout).map basis) ++ ((List.ofFn B.layout).map fun i=> -basis i)

lemma augments (A B : Degree H) (b : ℝ) : HeatP b A B=peck (reel A B)*HeatP b (origin A) (origin B):= by
  rw [show peck (reel A B)= _ from wing A B]; unfold HeatP paints feather; split
  · rename_i hv; rw [if_pos (show (origin A).paint=(origin B).paint from hv)]
    let L:= peck (List.map basis (raypath A B))
    have hf (i j) : press (raypath A B++[i,j]) (liturgy b)=L*press [i,j] (liturgy b):= by unfold press; rw [List.foldr_append]; exact bore ..
    have hx : raypath (origin A) (origin B)=[]:= rfl
    simp_rw [hf,hx,List.nil_append]; change ((-1:ℂ)^B.degree) • ( ( (if _ then L*_ else 0)-(if _ then L*_ else 0))-((if _ then L*_ else 0)-(if _ then L*_ else 0)))= _
    rw [smul_mul_assoc]; apply congr_arg
    unfold origin;dsimp only;rw [pow_zero,one_smul]; simp only [mul_sub, mul_ite, mul_zero]; rfl
  rename_i hv; rw [if_neg (show (origin A).paint ≠ (origin B).paint from hv),mul_zero]

lemma hollow (t : Fin n→E4) (F) : fling n t F=(staccato (List.ofFn t))*F:= by
  unfold fling staccato; simp_rw [List.map_ofFn,List.prod_ofFn]; ext1 i; rw [Pi.mul_apply, Finset.prod_apply]; rfl
lemma dizzy (L K : Degree H) (f) : parade L K f=staccato (reel L K)*f:= by rw [parade,hollow,hollow]; simp only [staccato,reel,List.map_append,List.map_ofFn, List.prod_append]; rw [mul_assoc]; congr

structure Shore (n j : ℕ) (f g : E4→ℂ) : Prop where
  near : ∃ c, Cast f n j 1 c
  halo : ∃ c, Cast g n j 1 c
  recoil : ∃ c,Cast (f-g) n (j+1) 1 c
lemma Shore.lace {i : ℕ} (a : Shore n i f g) (b : Shore n j h q) : Shore n (i+j) (f*h) (g*q):= by
  obtain ⟨⟨c,hc⟩,⟨t,ht⟩,⟨p,hp⟩⟩:=a; obtain ⟨⟨L,hL⟩,⟨g',hg⟩,⟨z,hB⟩⟩:=b
  refine ⟨⟨_,hc.multiply hL⟩,⟨_,ht.multiply hg⟩,?_⟩
  rw [show f*h-g*q=(f-g)*h+g*(h-q) by ring]
  have he:= hp.multiply hL; have H:= ht.multiply hB; rw [← add_assoc] at H
  rw [add_right_comm i] at he
  exact ⟨_,he.join H⟩
lemma Shore.rises (v : E4) (n : ℕ) : Shore n 1 (readD v) (chimes v):=
    ⟨vertex (tune v) (teleports v) _,vertex (glides v) (trill v) _,polarDay ((tune _).sub (glides _)) (by rw [teleports,trill,sub_self]) (transonic _) _⟩
lemma messages (l : List E4) (n) : Shore n l.length (staccato l) (peck l) := by
  induction l with
  | nil=>
    have hx : Cast (f:=1) n 0 1 1:= by
      refine ⟨zero_le_one, contDiffOn_const,fun i hi x _h he=> ?_⟩;by_cases h:i=0
      · subst i; simp
      change ‖iteratedFDeriv _ _ (fun _:E4=> (1:ℂ)) _‖*_ ≤ _; simp [iteratedFDeriv_const_of_ne h]
    refine ⟨⟨1,hx⟩,⟨1,hx⟩,0,by change Cast ((1:E4→ℂ)-1) _ _ _ _; rw [sub_self];exact ⟨le_rfl,contDiffOn_const,fun i hi x hx h=>by simp⟩⟩
  | cons a l I=>
    have ht: (a::l).length=1+l.length:=by simp [add_comm]
    rw [ht]; exact (Shore.rises a n).lace I
lemma starlight (l : List E4): ContDiff ℝ ∞ (staccato l):= by induction l with | nil=>exact contDiff_const|cons a l IH=>exact ContDiff.mul (tune a) IH
end YM.Next.Rank.Radian
