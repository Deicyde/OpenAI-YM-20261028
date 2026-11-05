import YM.TraceExtension.Margin.Corner
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Lattice Matrix Precision Laurent Labels Source RG Wilson StressFlux
open Finset Kits Pressure Terrace Terrace.Glade Work Further.PhysicalPeriodLimitF933
open Shunt Wicket Perfect Turret Weir Extra.Histories Next.Foundations Planned.PrimaryIntegral295 Place
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s:Side}{Φ:Peat G s}{H:Hol G}
open Zn
variable {F:Frame G 4}{Z:Frame G 5}{n:Side}{t:ℝ}{R:Rep G n}{J:Dart G n}
lemma stress_detect (h:G.Simple): Injective (labelStress (G:=G)):=by
    let L := Maxwell.standard (Labels.frames G)
    exact fun x y hh=> free_stress_inj (L:=L) h (funext fun a=>funext fun b=> congr_arg (fun v:RawTwo G=> fromPol (Climb.Bel L) (v.val a b)) hh)
lemma quart (v:Fin 3→ℝ)(hv:v 0=0)(hz:v 2=0)(a b:Axis): stress G (Fin.cons 0 v) a b=if a=b then (4*v 1) • square4 G else 0:=by
    rw[stress_of]; split_ifs; · change (0:ℝ) • _+v 0 • _+ v 1 • _= _; rw [hv,zero_smul,zero_smul,zero_add,zero_add]; unfold square4;module
    change v 2 • _=_; rw [hz,zero_smul]
lemma square_alive(h:G.Simple): square4 G ≠0:=by
   let v: Fin 3→ℝ:=![0,1,0]; let w:= Fin.cons (α:=fun _=>ℝ) 0 v
   intro hz; have hp: labelStress (G:=G) w=labelStress 0:=by rw[map_zero]; refine Subtype.ext (funext fun a=> funext fun b=>?_); change stress G w a b=0; unfold w; rw [quart v rfl rfl,hz];simp
   exact one_ne_zero (congr_fun (stress_detect h hp) (2:Fin 4))
-- ANY W4 field which is twig/Q horizon3: assesses zero.
abbrev bulkF (F:Frame G 4)(W: Axis → Axis → F.Coeff) : F.Coeff:= ∑ i:Axis,W i i
lemma TW(F:Frame G 4)(a:Axis)(g: CrG G n)(hv:Cubc R t (g 0))(h:Cubc R t (twig a g 0))(ht: Bounce g)(hx: Nonwrapping (tempQ t (n:=n)) 0)(hG:G.Simple)(hk: 40 ≤ n.val)(hn:4≤ R.p.order): DCard H F t (twig a g 0)=0:=by
    let c:= DCard H F t (twig a g 0); apply F.coords.symm.injective; apply label_ext; intro v; let V:loom G n:=⟨g 0,hv.silk⟩; let W:= (Kits.ivy (0:Site n) (v 0)); have hp:= steer0 (F:=g 0) a (1:ℤ) hv.silk.1 hv.puff.regular.sites hx (by decide) hk hG (v 0) W
    let Y:= starling V ((1:ℤ) • step a); have he : sheen (twig a g 0) W W=0:=by
       rw [show twig a g 0=(Y-V).val from ?_, ←anum,map_sub, anum,anum]; swap; · unfold twig; rw [zero_add,← ht.trap (step a)]; unfold Y; rw[one_smul];rfl
       rw [show sheen Y.val W W= sheen (g 0) W _ from shine_r a 1 hv.silk.1 hv.puff.regular.sites hx (by decide) hk hG 0 (v 0) (v 0),hp];exact sub_self _
    have hx := card_reads F (H:=H) (Real_regular h.puff.regular) hn hx; rw[vista4 h.silk.1 hG hx, he,show twig a g 0 1=0 from loom0 ⟨_,h.silk⟩];simp
-- purchases shared
abbrev R4(R:Rep G n)(t:ℝ)(f:Peat G n):= R.p.Regular (tempQ t) (filmR f)
lemma cheer {I:Type}(F:Frame G 4)(m:Finset I)(T:I→Peat G n)(hn:4≤ R.p.order)(h:∀ i∈m, R4 R t (T i)): (R4 R t (∑ i∈m,T i)) ∧
    DCard H F t (∑ i∈m,T i)=∑ i∈m,DCard H F t (T i):=by
    induction m using Finset.induction with
    | empty=> simp only [sum_empty]; rw [R4,DCard,show filmR (0:Peat G n)=0 from funext fun i=> by simp[filmR]]; rw[Push.Local.project_zero,map_zero]; exact ⟨Push.Local.regular_const 0,rfl⟩
    | insert i m hi ih=>
       have hp:=h i (mem_insert_self ..); obtain ⟨hT,hK⟩:=ih (fun j hj=> h j (mem_insert_of_mem hj)); rw[sum_insert hi,sum_insert hi]; unfold R4 DCard; rw[(plush (tempQ t) _ _ R 0).1]; refine ⟨regular_add hp hT,?_⟩; rw [Push.Local.project_add H _ hp hT hn,map_add]; rw [← hK]
lemma zero_club(F: Frame G 4)(v: Axis→Peat G n)(w: Axis → CrG G n)(hn:4 ≤ R.p.order)(hv:∀ i, Cubc R t (w i 0))(hp:∀ i,Cubc R t (twig i (w i) 0))(hR:∀ i,R4 R t (v i)) (hz:∀ i, Bounce (w i))(h:∑ i,v i=∑ i,twig i (w i) 0)(hG:G.Simple)(hs:40≤ n.val)(hx: Nonwrapping (tempQ t (n:=n)) 0): ∑ i,DCard H F t (v i) =0:=by
    rw [← (cheer F univ v hn (fun i _=>hR i)|>.2),h,(cheer F univ (fun i=>twig i (w i) 0) hn fun i _=> Real_regular (hp i).puff.regular).2]; refine sum_eq_zero fun i _=>TW F i _ (hv i) (hp i) (hz i) hx hG hs hn
-- `Plot` preserves trace zero and reality
lemma glaze(F : Frame G 4)(U:Axis→ Axis→ F.Coeff)(hp:bulkF F U=0):bulkF F (Plot (Prism F) U)=0:=by
    unfold bulkF; have hv(x:Motion)(i): rent*hued x i*hued x i=rent:=by unfold hued sign; split<;>ring
    rw [sum_congr rfl (g:=fun i=>∑ x:Motion,(rent:ℝ) • Prism F x (U (prev x i) (prev x i))) ?_]; rotate_left
    · intro i _; rw [plotEq]; exact sum_congr rfl (fun x _=> by rw[hv])
    rw[sum_comm]; apply sum_eq_zero; intro i _; rw[← smul_sum,← map_sum]; rw[show (∑ j, U (prev i j) (prev i j))=bulkF F U from Equiv.sum_comp i.1.perm.symm (fun j=>U j j),hp,map_zero,smul_zero]
lemma honestW(F: Frame G 4){w}{X:Sway G n}(he:Walt F Z H t X w)(hv:bulkF F (cardX F H t X)=0)(hG:G.Simple): rho hG (bareVector w)=0:=by
    let S:= Plot (Prism F) (cardX F H t X); have ht:= glaze F _ hv; unfold bulkF at ht; simp_rw [he.truth] at ht
    rw [←map_sum, mechanical_trace] at ht; have hz:= smul_eq_zero.mp (F.coords.injective (ht.trans (map_zero _).symm)); rw[rho_vector, neg_mul, (hz.resolve_right (square_alive hG)),neg_zero]
end YM.Trace.Margin
