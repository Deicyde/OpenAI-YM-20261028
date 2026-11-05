import YM.UVExtension.Eyelet.Wares
import YM.MergeProof.Chalet
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Rainfall
open Function Filter Set Lattice Wilson RG Labels Extra.Histories Source Bid Push
open Next.Foundations MergeProof Eyelet Planned.GuardedAtom Guard Local Concert Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c:Side}{n d:ℕ}{F:Frame G d}{B:SectionData F}{H:Hol G}{u v k t a b w σ x y:ℝ}{ι:Type}
section sugared
variable {P:BudgetPoint}{X: Support c} (h:Readable H B P c w)
local notation "B'"=> Config G c→ℂ
local notation "β"=> P.threshold
set_option quotPrecheck false
local notation "W"=> weighted H F (0:Site c) X β
include h
lemma adds {f g:B'}(hf:P.Regular X f)(hg:P.Regular X g): W (f+g)= W f+ W g:=by simp_rw [weighted, project_add _ _ hf hg h.order,map_add]
lemma enlarges {f:B'}(hf:P.Regular X f)(r:ℂ): W (r • f)= r • W f:=by simp_rw [weighted, project_smul _ _ _ hf h.order,map_smul]
lemma sips {f g:B'}(hf:P.Regular X f)(hg:P.Regular X g): W (f-g)= W f- W g:=(eq_sub_of_add_eq ((adds h (regular_sub hf hg) hg).symm.trans (congr_arg _ (sub_add_cancel ..))))
variable (F' :ι→ Config G c→ℂ)(p:ι→ℂ)
lemma shelly (hs:∀ i,P.Regular X (F' i)) (s:Finset ι): P.Regular X (∑ i∈s,p i • F' i)∧ W (∑ i∈s,p i • F' i) = ∑ i∈s,p i • W (F' i):=by
   induction s using Finset.induction with
   | empty => simp only [sum_empty]; exact ⟨(hot (o:=(0:Site c)) _ _).1,by simp [weighted]⟩
   | insert i s hi ih=> rw [Finset.sum_insert hi, Finset.sum_insert hi]; have hv:= regular_smul (p i) (hs i); exact ⟨regular_add hv ih.1,by rw [adds h hv ih.1, enlarges h (hs i), ih.2]⟩
lemma shiftsT {f g:B'}(hf:P.Regular X f)(hg:P.Regular X g)(hz:P.supBounds 0 X (f-g) t) :F.coeffSize (W f-W g) ≤ readPrice H F*t ∧ P.supBounds 0 (joint B 0 X) (Local.residual H B 0 X β f - Local.residual H B 0 X β g) (atomPrice H F w*t) ∧ ∀ U,‖rebate H B 0 X β f U-rebate H B 0 X β g U‖≤ atomPrice H F w*t:=by
   have hx:= regular_sub hf hg
   let z:=Local.residual H B 0 X β; have hv : z (f-g) = z f-z g:=by unfold z Local.residual; rw [sips h hf hg,map_sub]; abel
   rw [← sips h hf hg, ← show z (f-g) = Local.residual H B 0 X β f- Local.residual H B 0 X β g from hv]
   have hr:= charge_atom _ h hx hz
   refine ⟨weighted_bound _ _ _ hx h.order h.power hz,hr.1,fun U=> Eq.trans_le ?_ (hr.2 U)⟩
   apply congr_arg norm; have hh(q:B') : rebate H B 0 X β q=maskLinear β X q - Local.primary B 0 β (W q) - maskLinear β (joint B 0 X) (z q):=rfl
   exact congr_fun (show rebate H B 0 X β f-rebate H B 0 X β g=rebate H B 0 X β (f-g) from by simp_rw [hh]; rw [sips h hf hg, hv,map_sub,map_sub,map_sub]; abel) U
variable [Fintype ι]
omit h in
lemma tapSum {f:B'}(hs:∀ i,P.Regular X (F' i))(k:Tap P G 0 X)(h:(∑ i,p i • F' i)=f): k.read f=∑ i,p i * k.read (F' i):=by
    subst f; rw [Tap.read,Local.left_sum _ _ _ _ (fun i _=> (regular_smul _ (hs i)).smooth k.view k.live) k.card]; exact Finset.sum_congr rfl (fun i _=> Local.left_linear (p i • ContinuousLinearMap.id ℝ ℂ) k.poll ((hs i).smooth k.view k.live) k.card)
lemma grapes {f:B'}(hf:P.Regular X f)(hs:∀ i,P.Regular X (F' i))(hp:∀ U,Healthy β X U→ ∀ᶠ z in 𝓝 (0:Directions G c), f (increment U z)=∑ i,p i* F' i (increment U z)): let Z(k:B'):= rebate H B 0 X β k; let R(k:B'):= Local.residual H B 0 X β k
   W f=∑ i,p i • W (F' i) ∧ (∀ k:Tap P G 0 (joint B 0 X), k.read (R f)=∑ i,p i*k.read (R (F' i))) ∧ ∀ U,Z f U=∑ i,p i* Z (F' i) U:=by
   intro Z R; let g := ∑ i,p i • F' i; have ht(U):g U=∑ i,p i* F' i U:= Finset.sum_apply ..
   have hV(U) (hz:Healthy β X U): (f-g)∘ increment U=ᶠ[𝓝 0] (0:Directions G c→ℂ):=by
      filter_upwards [hp U hz] with z hh; simp only [Function.comp_apply,Pi.sub_apply, ht, hh, sub_self, Pi.zero_apply]
   have hb:P.supBounds 0 X (f-g) 0:=by
     refine tap_bound.mpr ⟨le_rfl,fun i=>?_⟩; rw [Tap.read, Local.left_congr (g:=fun _=>0) _ _ (hV i.view i.live),Work.G07.left_const]; split <;>simp
   have hL:=shelly h F' p hs Finset.univ; have hG:= shiftsT h hf hL.1 hb
   have he: W f= W g:= sub_eq_zero.mp (Work.G08.size_separates F _ (hG.1.trans (mul_zero ..|>.le)))
   have hq: ∑ i,p i • R (F' i)= R g :=by unfold R Local.residual; rw [hL.2,map_sum]; simp_rw [map_smul,smul_sub]; rw [Finset.sum_sub_distrib]
   have hy :∑ i,p i • Z (F' i)= Z g:=by
       have hZ(w:B'): Z w=maskLinear β X w - Local.primary B 0 β (W w) - maskLinear β (joint B 0 X) (R w):=rfl
       simp_rw [hZ]; rw [hL.2,← hq,show maskLinear β X g= _ from map_sum .., map_sum,map_sum]; simp_rw [smul_sub,map_smul]; rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]
   refine ⟨he.trans hL.2,fun k=> ?_,fun U=> ?_⟩
   · have hb: k.read (R f)= k.read (R g):=by
        have hp := (tap_bound.mp hG.2.1).2 k; rw [mul_zero] at hp
        have hR x(hx:P.Regular X x):= (convert_atom (0:Site c) h hx).1
        have hz:= norm_le_zero_iff.mp hp; let w:=R f-R g; have hj:w+R g=R f:= sub_add_cancel ..
        rw [← hj,Tap.read,Local.left_add (k:=P.order)]
        · exact add_eq_right.mpr hz -- may mismatched
        · exact (regular_sub (hR f hf) (hR g hL.1)).smooth _ k.live
        · exact (hR g hL.1).smooth _ k.live
        · exact k.card
     exact hb.trans (tapSum _ _ (fun i=>(convert_atom (0:Site c) h (hs i)).1) k hq)
   have h' := norm_le_zero_iff.mp ((hG.2.2 U).trans (mul_zero ..|>.le)); exact (sub_eq_zero.mp h').trans ((congr_fun hy.symm U).trans (Finset.sum_apply ..))
end sugared
section
variable {X: ℕ→Support c}{R:Rep G c} (h:Readable H B R.p c w)
structure Valid (M:Local.Raw F c) (X:ℕ→Support c)(R:Rep G c)(u:ℝ)(B:SectionData F)(H:Hol G)(w v:ℝ):Prop where
  halo : M.Format 0 X R
  costs : ∃ a b c':ℝ,Tare M 0 X H B R w u v a b c'
variable (ht:R.Lawful t a b σ u)(hv:0<v)
variable (K:Keeper R.p R.activities) {M:Local.Raw F c}(hx:Valid M X R u B H w v)
local notation "P" => R.p
local notation "Y"=> R.activities
-- one prescribed mapping.No choices through convergence.
def wallet (X:ℕ→Support c)(B:SectionData F)(M:Local.Raw F c)(H:Hol G):= mint (K.supply (fun i=> joint B 0 (X i))) M H
local notation "J"=> wallet (R:=R) K X B -- signature K first confirm
include ht h hv hx
lemma fits: Eligible (J M H) H R v:=by
   obtain ⟨a,b,c,hp⟩:= hx.costs; exact ⟨⟨K⟩, usage _ hx.halo ht h,_,(tab_mint _ hx.halo ht hv h hp).bound le_rfl⟩
lemma permitT: profile Y (J M H).forced=profile Y M.forced+ hook Y R.p.threshold (coda B H 0 X M R):=by obtain ⟨a,b,c,hq⟩:=hx.costs; exact budgetProfile _ hq hx.halo h ht hv
omit ht in
lemma handles: Dominated M.forced ∧ Summable (M.row 0 X H R.p.threshold) ∧ Dominated (fun i=> rebate H B 0 (X i) R.p.threshold (M.bulk i)):=by obtain ⟨a,b,c,hp⟩:= hx.costs; obtain ⟨hq,hQ⟩:= Local.Raw.dominated_pieces 0 h hx.halo (hp.income hv le_rfl); exact ⟨limb hp.packets,hq.of_norm,hQ⟩
variable [Fintype ι] {Z:ι→ Local.Raw F c}{p:ι→ℂ}
lemma orbit (hs:∀ i,Valid (Z i) X R u B H w v)
    (he:M.seed=∑ i,p i • (Z i).seed)(hF: ∀ j V,M.forced j V= ∑ i,p i*(Z i).forced j V)(hR:∀ j V,Healthy R.p.threshold (X j) V→ ∀ᶠ z in 𝓝 (0:Directions G c), M.bulk j (increment V z)=∑ i,p i*(Z i).bulk j (increment V z)):
    Eye (J M H) H R v= ∑ i,p i • Eye (J (Z i) H) H R v:=by
   have hM(i):= grapes (X:=X i) h (fun j=> (Z j).bulk i) p (hx.halo.regular i) (fun j=> (hs j).halo.regular i) (hR i)
   have hvX(i):= fits h ht hv K (hs i)
   have he' i:= handles h hv (hs i)
   rw [(fits h ht hv K hx).vistas]; simp_rw [fun i=>(hvX i).vistas]; apply Prod.ext
   · rw [Prod.fst_sum]; change M.seed+∑' i : ℕ,M.row 0 X H R.p.threshold i= ∑ j,p j • ((Z j).seed+∑' i,(Z j).row 0 X H R.p.threshold i); have hp(i): M.row 0 X H R.p.threshold i = ∑ j,p j • (Z j).row 0 X H R.p.threshold i:= (hM i).1
     simp_rw [hp,he,smul_add,Finset.sum_add_distrib]; rw [Summable.tsum_finsetSum]; swap; · intro i _; exact (he' i).2.1.const_smul _
     rw [add_right_inj]; exact Finset.sum_congr rfl fun i _=> (he' i).2.1.tsum_const_smul _
   rw [Prod.snd_sum]; apply Prod.ext
   · rw [Prod.fst_sum]; apply Roc.ext; intro i y
     let z:=joint B 0 (X i.2)
     have hh:∀ K':Local.Raw F c, graft (J K' H) i = if i.1.val=z then Local.residual H B 0 (X i.2) R.p.threshold (K'.bulk i.2) else 0:=fun _=>rfl
     change gaze _ _ _ _ _ (fits h ht hv K hx).tollE= gaze _ _ _ _ _ (∑ i,p i • (hvX i).tollE)
     rw [map_sum]; simp_rw [map_smul,Eligible.take, hh]; split_ifs with hB; swap; · simp [Tap.read,show (0:Config G c→ℂ)=(fun _=>0) from rfl, Work.G07.left_const]
     have hφ:y.read (Local.residual H B 0 (X i.2) R.p.threshold (M.bulk i.2))=∑ j,p j*y.read (Local.residual H B 0 (X i.2) R.p.threshold ((Z j).bulk i.2)):=by
        obtain ⟨V,hV,l,hl,hr⟩:=y; rw [hB] at hV; exact (hM i.2).2.1 ⟨V,hV,l,hl,hr⟩
     rw [hφ,Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> mul_left_comm ..
   rw [Prod.snd_sum]
   apply Coil.ext; intro i U
   change tire _ _ _ (fits h ht hv K hx).tollK= tire _ _ _ (∑ i,p i • (hvX i).tollK); rw [map_sum]; simp_rw [map_smul,Eligible.make, permitT h ht hv K hx, fun i=> permitT h ht hv K (hs i), Pi.add_apply]
   have hz:profile Y M.forced i.val U= ∑ j,p j * profile Y (Z j).forced i.val U:=by
      unfold profile cram; simp_rw [hF]; rw [Summable.tsum_finsetSum]; swap; · intro j hj; exact ((he' j).1.summable U|>.comp_injective Subtype.val_injective).mul_left _
      simp_rw [tsum_mul_left]
   have hg(q:Support c):coda B H 0 X M R q U= ∑ j,p j * coda B H 0 X (Z j) R q U:=by
      unfold coda clipSum cram; simp_rw [show ∀ i,rebate H B 0 (X i) R.p.threshold (M.bulk i) U= _ from fun i=>(hM i).2.2 U]; rw [Summable.tsum_finsetSum]; swap; · intro j hj; exact ((he' j).2.2.summable U|>.comp_injective Subtype.val_injective).mul_left _
      simp_rw [tsum_mul_left]
   have ht': hook Y R.p.threshold (coda B H 0 X M R) i.val U= ∑ j,p j*hook Y R.p.threshold (coda B H 0 X (Z j) R) i.val U:=by
       unfold hook; simp_rw [hg,Finset.sum_mul,Finset.mul_sum]; rw [Finset.sum_comm]; simp_rw [mul_assoc]
   rw [hz,ht',← Finset.sum_add_distrib,Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _=> by rw [smul_eq_mul]; ring)
end
end YM.UVExtension.Rainfall
