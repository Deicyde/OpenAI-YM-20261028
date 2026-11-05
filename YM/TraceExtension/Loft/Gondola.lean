import YM.TraceExtension.Loft.Tips
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n:ℕ}{σ τ A C D μ ε:ℝ}
variable (d i:Axis)(q:G.ColorIndex)
lemma yard_turn {F:Peat G f}(h:Contours F)(hp:d≠i): yard d i q (F∘ input G f) = yard 0 1 q (F∘input G f):=by
    unfold yard Lamp.cob; obtain ⟨u,ht,hx⟩:=permTrip d i 0 1 hp (by decide)
    apply congr_arg _; apply congr_arg _; funext j; let s:= platey u
    let x:= -(wrap f (ra d j)); let a:= mood G i q
    have he:s.act x= -(wrap f (ra 0 j)):=by
        unfold x; rw[Signed.act_neg,wrap_signed]; congr 3
        ext1 b; obtain ⟨i,rfl⟩:=s.perm.surjective b; rw [s.act_at]; by_cases he:i=d
        · subst i; simp [*,s,platey,ra]
        simp [s,platey,ra,he,← ht]
    have hz:= shark_her h x i i q q s
    have hL:reflectFee s (mon (-s.act x)) i=1:=by simp[reflectFee,s,platey]
    have hr: reflectFee s (mon (s.act x)) i=1:=by simp[reflectFee,s,platey]
    rw[hL,hr,show s.perm i=1 from hx,one_mul,one_mul] at hz
    have ha: clipP i q (F∘input G f) (wrap f (ra d j)) x=clipP 1 q (F ∘input G f) (wrap f (ra 0 j)) (-(wrap f (ra 0 j))):=by
       unfold clipP
       generalize hy:x=z at *
       rw [show wrap f (ra d j)= -z from ?_]; swap; · rw [← hy]; simp [x]
       let b:= wrap f (ra 0 j)
       change beat _ 0 2 _= beat _ 0 2 ![relay b _,relay (-b) _]
       rw [← show _=b from neg_neg b,neg_neg (-b), ray_shark h z, ray_shark h (-b)]
       rw[he] at hz; exact congr_arg _ hz.symm
    exact congr_arg _ ha
lemma jury {F:Peat G f}(h:Contours F) : suite (fun d i=> yard d i q (F∘input G f))=(12:ℂ)*yard 0 1 q (F∘input G f):=by
    let H:=F∘input G f; let A:=yard 0 1 q H
    unfold suite; rw[show (∑ d:Axis,∑ i:Axis,if d=i then 0 else yard d i q H)=∑ d:Axis,∑ i:Axis,if d=i then 0 else A from ?_]
    · simp [Fin.sum_univ_succ]; ring
    refine sum_congr rfl (fun d _=> sum_congr rfl (fun i _=>?_)); by_cases he:d=i <;> simp[he,A,H]; exact yard_turn d i q h he
lemma exchange_tip {P:ℝ →Maze G f}(h: ContDiffAt ℝ ω (uncurry P) 0)(p q:Phase (Lines G f 1)):
    let K:= fun z=> fderiv ℝ (fun s:ℝ=> P s z) 0 1
    HasDerivAt (fun t:ℝ=> beat (P t) 0 2 ![p,q]) (beat K 0 2 ![p,q]) 0:=by
    intro K; let A t p q:=beat (P t) 0 2 ![p,q]; let V p q:= beat K 0 2 ![p,q]
    have hx(v w:Link G f) : HasDerivAt (fun t:ℝ=> A t (axes v) (axes w)) (V (axes v) (axes w)) 0:=by
        have he(F: Link G f→ℝ): beat F 0 2 ![axes v,axes w]=(↑(iteratedFDeriv ℝ 2 F 0 ![v,w]):ℂ):=by
            rw[show (![axes v, axes w]:Fin 2→_)=axes ∘ (![v,w]:Fin 2→ _) from funext fun i=>by fin_cases i <;> rfl];exact beat_real ..
        unfold V A K; simp_rw[he]; rw[Det.exchange_bend h 1]
        let S(t):=iteratedFDeriv ℝ 2 (P t) 0 ![v,w]; refine Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (0:ℝ) (show HasDerivAt S (fderiv ℝ S 0 1) 0 from DifferentiableAt.hasDerivAt (ContDiffAt.differentiableAt (n:=ω) ?_ (by simp)))
        let Y(t:ℝ)(x):=fderiv ℝ (P t) x w
        have ht: (fun t:ℝ=> fderiv ℝ (Y t) 0 v)=ᶠ[𝓝 0] S:=by
           filter_upwards[(show Tendsto (fun t=> (t,(0:Link G f))) (𝓝 (0:ℝ)) (𝓝 0) from tendsto_id.prodMk_nhds tendsto_const_nhds).eventually (h.eventually (by simp))] with a ha
           exact divided v w (ha.comp (f:=fun z=>(a,z)) _ (by fun_prop))
        exact ContDiffAt.congr_of_eventuallyEq ((analytic_r (analytic_r h w) v).comp (f:=fun t=>(t,(0:Link G f))) 0 (by fun_prop)) ht.symm
    have hl (F:ℝ→Phase (Lines G f 1)→ℂ)(f':Phase (Lines G f 1)→ℂ)(he: ∀ i,Leads (F i))(hy: Leads f')(ht:∀ v,HasDerivAt (fun t:ℝ=> F t (axes v)) (f' (axes v)) 0)(p) : HasDerivAt (fun t:ℝ=>F t p) (f' p) 0:=by
        let v:=fun i=>(p i).re; let w:=fun i=> (p i).im
        rw [show p=axes v+Complex.I • axes w by funext i; simp[axes,v,w];rw [mul_comm Complex.I, Complex.re_add_im],hy]; rw[show (fun t:ℝ=>F t (axes v+Complex.I • axes w))= _ from funext fun i=> (he i v w)]; exact (ht v).add ((ht w).const_smul Complex.I)
    exact hl (fun i p=> A i p q) (fun x=>V x q) (fun i=> left_beat _ _) (left_beat _ _) (fun u=>hl (fun i y=>A i (axes u) y) (V (axes u)) (fun i=>right_beat _ _) (right_beat _ _) (hx u) _) _
lemma exchange_y {P:ℝ →Maze G f}{K:Maze G f}(h: ContDiffAt ℝ ω (uncurry P) 0)(he:(fun z=> fderiv ℝ (fun s:ℝ=>P s z) 0 1)=ᶠ[𝓝 0] K): HasDerivAt (fun t:ℝ=> yard d i q (P t)) (yard d i q K) 0:=by
    have ht(p q:Phase (Lines G f 1)):=exchange_tip h p q
    let A(j:ℤ):=wrap f (ra d j); let C:ℂ:=(pitchf f:ℂ)⁻¹ ^(2:ℕ)
    have hv(j:ℤ): HasDerivAt (fun t:ℝ=> C • clipP i q (P t) (A j) (-(A j))) (C • clipP i q K (A j) (-(A j))) 0:=by
       rw [← clip_eq i q (he.iteratedFDeriv ℝ 2 |>.eq_of_nhds)]; exact (ht _ _).const_smul C
    exact ((((hv 1).sub ((hv 0).const_smul (2:ℂ))).add (hv (-1))).const_smul ((1/2:ℂ))).const_smul ((Fintype.card (Site f):ℂ)⁻¹)
end YM.Trace.Loft
