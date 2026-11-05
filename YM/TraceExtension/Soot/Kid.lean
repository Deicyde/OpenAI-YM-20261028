import YM.TraceExtension.Soot.Overland
import YM.MergeProof.North.Clause
import YM.MergeProof.Bungalow
/-! Singleton shipping. rebate closure cost after shrinking w at the seam. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I : Type} [Fintype V][DecidableEq V]{B:Census V}{G:Gauge}{n:Side}
open GridApprox.Nil Local Extra.Trajectories Source Extra.Multi
variable {o:V→Site n}{x y u:Census V} {w:V→ℝ} {t e a b:ℝ}
lemma pink {i:Box n}{F L : Config G n→Poly B}(hf:Flow o i F t)(hl:Flow o i L t): Flow o i (F+L) t:=by
    refine ⟨⟨fun U V h ht=> congr_arg₂ (· + ·) (hf.home _ _ h ht) (hl.home _ _ h ht), fun i U=>congr_arg₂ (· + ·) (hf.turns ..) (hl.turns ..),fun j=>(hf.me j).add (hl.me j),fun U=>GridApprox.Nil.scope_plus (hf.scope U) (hl.scope U)⟩,fun U ht=> ?_⟩
    by_cases he : F U=0; swap; · exact hf.permits U he
    exact hl.permits _ fun h=> ht (by rw[Pi.add_apply,he,h]; simp)
lemma buoy {p:I→Support n}{F L:I→ Config G n→Poly B}{k:ℕ}(hw:∀ i,0<w i)(h:Towed w p F k t a)(hx:Towed w p L k t b) : Towed w p (F+L) k t (a+b):=by
    obtain ⟨g,hg,G,h⟩:= h;obtain ⟨q,hq,Q,hx⟩:=hx
    have he:Hit p k (fun i=>g i+q i) t (a+b):=by
        intro x; convert Budget.plus (G x) (Q x) using 1; funext i; split_ifs <;> ring
    refine ⟨g+q,hg.add hq,he,fun i=>?_⟩; obtain ⟨c,hc,h,h₀⟩:=h i; obtain ⟨d,hd,hx,h₁⟩:=hx i
    refine ⟨c+d,add_nonneg hc hd,fun U j=>?_,?_⟩
    · simp only [Pi.add_apply,Poly.part_plus]; exact (norm_add_le ..).trans (add_le_add (h U j) (hx U j))
    unfold wordsPrice; simp only[Pi.add_apply,mul_add,Finset.sum_add_distrib]; exact add_le_add h₀ h₁
variable (R:Rep G n)(o:V→Site n)(w:V→ℝ)(B:Census V)(K:V→ℕ→ Config G n→ℂ)(hw:∀ i,0<w i)
    (f:V→ℝ)(h:∀ i, ForceFormat R.p R.activities (o i) (K i)) (hp:∀ i,ForceCost R.p R.activities (K i) (f i))
def quillK (i:V×ℕ) (U : Config G n) : Poly B:= Poly.send (B.fire i.1) (K i.1 i.2 U)
def kilns (p:Box n) (U : Config G n):= Mach B (fun i=> profile R.activities (K i) p U)
local notation "g"=>barcode R.activities
include hp
lemma vitalK (p:Box n)(U:Config G n): kilns R B K p U=tally (g∘Prod.snd) (quillK B K) p U:=by
    have he : Summable (fun i:V×ℕ=> quillK B K i U):= Summable.of_norm ((summable_prod_of_nonneg fun i=>norm_nonneg _) |>.mpr ⟨fun i=> (?_),Summable.of_finite⟩)
    · ext j; let v:=fun p:V×ℕ=>quillK B K p U; let J:={i:V×ℕ// (g∘ Prod.snd) i=p}; unfold kilns tally Mach; rw [Poly.part_sum,Poly.share (show Summable (fun i:J=> quillK B K i.val U) from he.comp_injective Subtype.val_injective)]
      change _= cram (g∘Prod.snd) (fun i=>(v i).part j) p; rw [expand_eq]; rotate_left
      · let F:= fun i:V × ℕ=> if g i.2=p then (v i).part j else 0; have hh : Summable F:=by
          have hu:Summable (fun i=>(v i).part j):= ((Poly.get j).hasSum he.hasSum).summable
          convert! hu.indicator { x| g x.2=p} using 1; ext1 i; by_cases h:g i.2=p <;> simp [F,h]
        change _=∑' i,F i
        rw [show ∑' (i: V×ℕ),_= _ from hh.tsum_prod,tsum_fintype]; refine sum_congr rfl (fun i _=> ?_); unfold F; simp only [v,quillK,Poly.part_send]; split_ifs with hj
        · unfold profile; rw [expand_eq]
        · simp
    obtain ⟨v,h,hV⟩:= hp i
    have hh': Summable (fun k:ℕ=> Poly.price (fun _=>1) (quillK B K (i,k) U)):= (Local.sumBudget_uncharge (fun i=>(hV i).1) h).2.1.of_nonneg_of_le (fun i=>Poly.nonnegative (fun _=>zero_lt_one) _) (fun j=>by unfold quillK; simp only [Poly.solo,Poly.solo_toll,one_mul]; exact (hV j).2 U)
    exact ((Poly.budgeted (w:=fun _=>1) (fun _=>zero_lt_one) hh' (fun _=>le_rfl)).1).norm
include h hw
lemma brightK {m:ℕ} (he:Occupancy o m)(ht:0≤e)(ht':∀ i,w i*f i ≤ e) : (∀ p,Flow o p (kilns R B K p) R.p.threshold) ∧ Towed w Prod.fst (kilns R B K) R.p.B (R.p.supportExponent-1) (m*siteFactor R.p.B*e):=by
    have hp':=hp; choose c hc hh using hp
    let k(j:V×ℕ):ℝ:=if o j.1∈ (g j.2).1 then c j.1 j.2 else 0
    have hg(j):0≤ k j:=by unfold k; split; exact (hh _ _).1; rfl
    let S:= g ∘ Prod.snd (α:=V); let a(i:V×ℕ):=w i.1*k i; let p(i):= (S i).1; have hQ(j):0≤ a j:= mul_nonneg (hw _|>.le) (hg _)
    have hG(i:V×ℕ) : Loci w (quillK B K i) (a i):=by
        change Loci _ _ (_ * _); refine (show Loci w _ (w i.1*k i) from ?_); rw [← Poly.solo_toll (R:=B) (w:=w) i.1]; refine satin (K i.1 i.2) _ _ (hg i) (fun U=>?_); unfold k; split; exact (hh _ _).2 _; next ht=> rw [not_not.mp (mt ((h i.1).carried i.2) ht)]; simp
    have he':Hit p R.p.B a (R.p.supportExponent-1) (m*siteFactor R.p.B*e):=by
        refine root_hit he hQ ht (mode:=fun j:V×ℕ=>{j.1}) (fun i hv=> ?_) (fun i=>?_)
        · have hx:o i.1∈(g i.2).1:=by by_contra h; unfold a k at hv; rw[if_neg h,mul_zero] at hv;exact lt_irrefl _ hv
          exact ⟨i.1,mem_singleton_self _,hx⟩
        refine Budget.certify (fun j=> ?_) (fun s=>?_)
        · split; exact mul_nonneg (Real.exp_pos _).le (hQ _);exact le_rfl
        refine le_trans ?_ (ht' i); let v (j:ℕ):= w i*R.p.mass (Local.patch R.activities j) (c i j)
        have hx(j:ℕ):0≤ v j:=mul_nonneg (hw i|>.le) ((hc i).1 j)
        let T:= s.filter (fun j:V×ℕ=>i=j.1); simp_rw [Finset.mem_singleton,sub_add_cancel, ← sum_filter]; refine le_trans ?_ (Budget.cap (Budget.scale (hc i) (hw i|>.le)) (T.image Prod.snd)); change _ ≤∑ j∈T.image Prod.snd,v j
        rw [sum_image]; swap; · exact fun j hj k hk he=> Prod.ext ((mem_filter.mp hj).2.symm.trans (mem_filter.mp hk).2) he
        refine sum_le_sum fun j hj=> ?_; have hj':j.1=i:= (mem_filter.mp hj).2.symm; refine le_trans ?_ (le_refl (v _)); unfold a k; split
        next h=> unfold p S v BudgetPoint.mass; rw [hj']; rw [mul_left_comm]; rfl
        next h=> rw [mul_zero,mul_zero]; exact hx j.2
    have hS: Summable a:= by
        refine Summable.of_norm ?_; simp only [Real.norm_of_nonneg (hQ _)]; apply (summable_prod_of_nonneg hQ).mpr; refine ⟨fun i=>?_ ,Summable.of_finite⟩
        apply ((Local.sumBudget_uncharge (fun j=> (hh i j).1) (hc i)).2.1.mul_left (w i)).of_nonneg_of_le (fun j=>hQ _) (fun j=> ?_); unfold a k; split; exact le_rfl; rw [mul_zero]; exact mul_nonneg (hw _|>.le) ((hh _ _).1)
    let Q:= quillK B K; have hT:Towed w (Prod.fst ∘ S) Q _ _ _:= ⟨a,hS,he',hG⟩
    rw [show kilns R B K=tally S Q from funext fun p=> funext fun U=> vitalK R B K f hp' p U]; refine ⟨transitK S (r:=id) (fun i=> ?_) (fun U=>(hT.repair hw _).2), towing S Q hT hw⟩
    let q:= i.1; let Z:= K i.1 i.2; let L:= R.activities.forced i.2
    refine ⟨⟨fun U V hu hv=> congr_arg (Poly.send (B.fire i.fst)) ((h _).supported _ _ _ hu hv), fun v U=> congr_arg (Poly.send (B.fire i.fst)) ((h _).invariant _ _ _),fun p=>?_,fun U=>?_⟩, fun U ht=>?_⟩
    · simp_rw [Q,quillK,Poly.part_send]; split; exact (h _).borel _; exact measurable_const
    · by_cases hx : Z=0; change Scoped _ (Poly.send _ (Z U)); rw [hx,show (0:Config G n→ℂ) U=0 from rfl, Poly.send_zero]; exact fun _ _=>rfl
      apply scope_send; intro j hj; exact (Finset.mem_singleton.mp hj).symm ▸ (h _|>.carried _ hx)
    exact ⟨(h _|>.forcing i.2 U (fun he=> ht (show Poly.send _ (K i.fst i.snd U) = _ from by rw [he,Poly.send_zero]))).1,L.inventory_ne,L.inventory_sup⟩
end YM.MergeProof.Accent
