import YM.MergeProof.Fruit
import YM.MergeProof.Tally
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge  Accent Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open Extra.Trajectories Planned.GuardedAtom
variable (w':Wing)
    {s:B.Mode}
    (H:Config G f→ℂ)
    (v:V→ℝ){d h e b c':ℝ}{o: V→Site f}

lemma couple (h1 : UsesFinal R.p.threshold (w'.support R) H)(ht:∀ U,H U≠0→ w'.qualifies R U)(hb:w'.blank R)(hm: Measurable H)(hf:GaugeInvariant H)(hp:∀ U,‖H U‖ ≤ b)(he:s.val.Nonempty) :∃ P:Bool→ Hat B R,(∀ i,WKey (P i)=w' ∧ (P i).s=s) ∧ ∑ i,fare (P i) v= 2*(Poly.toll v s*b) ∧ ∀ U,∑ i, amount (P i) U=Poly.send s (H U):=by
   let p(L:ℂ →L[ℝ] ℝ)(g:∀ i,‖L i‖≤ ‖i‖): Leaf R:= {
      turn:=w'
      weight:=b
      ingredient:= fun i=> L (H i)
      scopedR:=fun U V hx ht=> congr_arg _ (h1 U V hx ht)
      grant:= fun U hu=> ht U (fun h=>hu (by rw [h,map_zero]))
      blank:=hb
      glows:=fun k U=>congr_arg _ (hf k U)
      borel:=L.continuous.measurable.comp hm
      earn:=fun i=>(g _).trans (hp i) }
   let t:Hat B R:= ⟨p Complex.reCLM (fun i=> Complex.abs_re_le_norm _),s,he,1⟩; let u:Hat B R:=⟨p Complex.imCLM (fun i=>Complex.abs_im_le_norm _),s,he,Complex.I⟩; let f(x:Bool): Hat B R:= if x then t else u
   have hT : f true=t:=by simp [f]
   have hU : f false=u:=by simp [f]
   refine ⟨f,fun i=> ?_,?_,fun U=> ?_⟩
   · cases i; rw [hU]; exact ⟨rfl,rfl⟩; rw [hT]; exact ⟨rfl,rfl⟩
   · rw [Fintype.sum_bool,hT,hU]; simp only [fare,sumFee,t,u,p,norm_one,Complex.norm_I]; ring
   rw [Fintype.sum_bool,hT,hU,varnish,varnish]; dsimp only [u,t,p]; rw [← Extra.Trajectories.send_add,mul_one]; congr 1; exact Complex.re_add_im _
-- trim to active mode correct locality & plate. statement from W produced when only if f i≠0. land fees.Current
variable [Fintype ι] {X:ι→Support f}{F:ι→ Config G f→Poly B}
def Vivid (F:ι→ Config G f→Poly B) (i:ι)(p:B.Mode):=∃ U,(F i U).part p ≠0
abbrev VividId (F:ι→ Config G f→Poly B) := Σ i, {p:B.Mode // Vivid F i p} × Bool -- fine.location
lemma alarm (hv:∀ i,0<v i) {g:ι→Wing}
    (h:∀ i,F i≠0→ (g i).support R=X i ∧ (g i).blank R)(ht:∀ i U,F i U≠0→ (g i).qualifies R U)
    (hp:∀ i,Borne o (X i) (F i) R.p.threshold)(hx:∀ i U,rises (F i U))(he:Towed v X F R.p.B d b):∃ (P:VividId F→ Hat B R),
    (∀ i,WKey (P i)=g i.fst ∧ (P i).s=i.2.1.val) ∧ Offer o P v R.p.B d (2*b) ∧ ∀ i U,∑ j:{i':B.Mode // Vivid F i i'} × Bool, amount (P ⟨i,j⟩) U= F i U :=by
   let A(i):= {p:B.Mode// Vivid F i p}; have hh(i) (x:A i): F i≠0:=by obtain ⟨y,hy⟩:=x.property;exact fun ht=> hy (by rw [ht];rfl)
   obtain ⟨w,hw,hW,hB⟩:=he
   choose f hf hs hP using hB
   have hI(i)(x:A i): 2 ≤ x.val.val.card:=hx i _ _ x.property.choose_spec
   obtain ⟨P,HP,HQ,Hh⟩ : ∃ (u : ∀ i,A i→ Bool→Hat B R), (∀ i p j,WKey (u i p j)=g i ∧ (u i p j).s=p.val) ∧ (∀ i p,∑ l,fare (u i p l) v = 2*(Poly.toll v p.val*f i p.val))∧∀ i p U,∑ l,amount (u i p l) U=Poly.send p.val ((F i U).part p.val):=by
      have he i (p:A i): UsesFinal R.p.threshold ((g i).support R) (fun U=> (F i U).part p.val):= (h i (hh i p)).1.symm ▸ (fun U V hx ht=> congr_arg (fun f:Poly B=> f.part p.val) ((hp i).home U V hx ht))
      choose u hu hU hT using fun i p=> couple (R:=R) (g i) (s:=(p:A i).val) (fun U=> (F i U).part p.val) v (he i p) (fun U hv=> ht i U (fun h=> hv (by rw [h];rfl))) (h i (hh i p)|>.2) (hp i|>.me _) (fun t U=> congr_arg (fun f:Poly B=> f.part p.val) ((hp i).turns t U)) (fun U=> hs i U _) (Finset.card_pos.mp (show 0 < p.val.val.card from (Nat.succ_pos 1).trans_le (hI ..)))
      exact ⟨u,hu,hU,hT⟩
   let P' (i:VividId F): Hat B R:= P i.1 i.2.1 i.2.2
   have hz i (j:A i×Bool): (P' ⟨i,j⟩).M.crest=X i:=by rw [show (P' ⟨i,j⟩).M.crest=(g i).support R from congr_arg (fun i:Wing=>i.support R) (HP i j.1 j.2).1]; exact (h i (hh i j.1)).1
   -- CORE
   refine ⟨P',fun i=>HP ..,⟨fun i=>?_,fun i=>?_⟩,fun i U=>?_⟩
   · rcases i with ⟨i,j⟩; rw [hz,show (P' ⟨i,j⟩).s=j.1.val from (HP ..).2]; exact (hp i).place _ _ j.1.property.choose_spec
   · refine ⟨fun i=>?_,Summable.of_finite,?_⟩
     · dsimp only; split; exact mul_nonneg (Crew v hv) (Real.exp_pos _).le;rfl
     apply le_trans _ (mul_le_mul_of_nonneg_left (Extra.Multi.Budget.cap (hW i) univ) zero_le_two)
     rw [tsum_fintype,Fintype.sum_sigma, Finset.mul_sum]; refine Finset.sum_le_sum fun j _=>?_ ; dsimp only
     by_cases hx:i∈X j
     · let Z:= Real.exp (d*coverNumber R.p.B (X j)); have hN(y : A j × Bool):
           (if i∈ (P' ⟨j,y⟩).M.crest then fare (P' ⟨j,y⟩) v*Real.exp (d*coverNumber R.p.B (P' ⟨j,y⟩).M.crest) else 0)= Z*fare (P j y.1 y.2) v:=by rw [if_pos (show i∈ _ from hz j y|>.symm ▸ hx), hz]; exact mul_comm ..
       rw [if_pos hx,Finset.sum_congr rfl (fun i _=>hN i), ← mul_sum,Fintype.sum_prod_type]; simp_rw [HQ]; rw [← Finset.mul_sum];
       have hu : ∑ i : A j, Poly.toll v i.val*f j i.val≤w j:=by
          rw [← Finset.sum_subtype (p:=Vivid F j) ((univ:Finset B.Mode).filter fun p=> Vivid F j p) (fun i=>by simp) (fun i=> Poly.toll v i*f j i)]; exact (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun p _ _=> mul_nonneg (Poly.worth hv _).le (hf ..)).trans (hP j)
       refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu zero_le_two) (Real.exp_pos _).le).trans_eq ?_; ring
     rw [if_neg hx,mul_zero,sum_eq_zero]; intro y _; exact if_neg ((hz j y).symm ▸ hx) -- cast
   rw [Fintype.sum_prod_type]; simp_rw [P',Hh];
   conv_rhs => rw [← Poly.studs (F i U)]
   classical
   refine (sum_subtype (p:=Vivid F i) (s:= Finset.univ.filter (Vivid F i)) (fun i=>by simp) (fun j=>Poly.send j ((F i U).part j))).symm.trans (sum_subset (subset_univ _) fun j _ h=> ?_)
   have he: (F i U).part j=0:=Classical.byContradiction fun H=> h (mem_filter.mpr ⟨mem_univ _,(show Vivid F i j from ⟨U,H⟩)⟩); simp [he]
end YM.MergeProof.Menu
