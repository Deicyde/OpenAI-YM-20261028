import YM.TraceExtension.Perfect.Flo
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG RG.Supply Wilson Finset Push.Uniform Planned.PrimaryIntegral295 Next.Free Org Input Extra.Histories
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{R:PathData G}

-- torus loans
structure Estate (x:Site f)(J:Acr G f→ℝ)(v:ℝ)(d:ℕ→ℝ) :Prop where
 values j : j≤4→2≤j→cost (landW x) v 4 0 (leaf J 0 j) ≤ d j
structure Testify (x:Site f)(J:Acr G f→ℝ)(K:Tit G→Tit G→ℝ)(d:ℕ)(ε:ℝ): Prop where
 bill s t (ht:ScoreG s+ScoreG t≤d): |iteratedFDeriv ℝ 2 J 0 ![ballad s x,ballad t x]-K s t|≤ ε

structure Viz (K:Dart G f)(p:Clip)(R:PathData G)(v:ℝ)(d f':ℕ→ℝ)(ε:ℝ): Prop where
 sound : K.Sound R p
 J a b x : Estate x (ballX (K.J a b x)) v d
 Y a x: Estate x (bottom (K.Y a x)) v d
 E a x: Estate x (ballX (K.E a x)) v f'
 plum a x: Estate x (ballX (K.Q a x)) v d
 mint a b j x:Estate x (ballX (K.twist a b j x)) v d
 ox a b x: Testify x (ballX (K.J a b x)) (fun i j=>north i j 0 a b) 4 ε
 orb a x : Testify x (bottom (K.Y a x)) (missY a) 5 ε

variable {W:Type}{F:Filter W}{n: W→Side}{u:ℝ}{d e:ℕ→ℝ} {J:∀ w,Site (n w)→Acr G (n w)→ℝ}
private lemma any {P:∀ w,Site (n w)→Prop} (h:∀ x:∀ w,Site (n w), ∀ᶠ w in F,P w (x w)) : ∀ᶠ w in F,∀ x,P w x:=by
 let X(w): Site (n w):= if ht:∃ x,¬ P w x then ht.choose else 0
 refine (h X).mono fun w hw x=>?_ ; by_contra he; have hi:∃ x,¬ P w x:=⟨_,he⟩; exact hi.choose_spec (show P w hi.choose from (by unfold X at hw; rw [dif_pos hi] at hw; exact hw))
lemma cash_ear (H:∀ x i,i≤4→2 ≤ i→Ear F x (fun w=>J w (x w)) u i (d i)) (h:∀ i,i≤4→2 ≤ i→d i<e i):∀ᶠ w in F,∀ x, Estate x (J w x) u e:=by
 apply Perfect.any (fun x=> ?_)
 have hp(k:ℕ)(hk:k≤4)(he:2≤ k):∀ᶠ w in F,cost (landW (x w)) u 4 0 (leaf (J w (x w)) 0 k) ≤ e k:=by have ht:= (H x k hk he).fee (e k-d k) (sub_pos.mpr (h _ hk he)); simpa only[add_sub_cancel] using ht
 filter_upwards [hp 2 (by decide) le_rfl,hp 3 (by decide) (by decide), hp 4 le_rfl (by decide)] with w hv hy hz; refine ⟨fun i hi hh=>?_⟩; interval_cases i<;> assumption
lemma cash_tip {K:Tit G→Tit G→ℝ}{d:ℕ}(H:∀ x,Tip F x (fun w=>J w (x w)) K d)(ε:ℝ)(h:0<ε):∀ᶠ w in F,∀ x, Testify x (J w x) K d ε:=by
 refine Perfect.any fun x=>?_ ; suffices hh: ∀ᶠ w in F,∀ s t:Tit G,ScoreG s+ScoreG t ≤ d→ |iteratedFDeriv ℝ 2 (J w (x w)) 0 ![ballad s (x w),ballad t (x w)] - K s t| ≤ ε by exact hh.mono (fun i h=>⟨h⟩)
 refine eventually_all.mpr fun s=> eventually_all.mpr fun t=>?_ ; by_cases he:ScoreG s+ScoreG t ≤ d
 · exact ((H x).sees.taste s t he |>.eventually (Metric.ball_mem_nhds _ h)).mono (fun w hh _=> ((by simpa only [Real.dist_eq] using (Metric.mem_ball.mp hh).le)))
 exact Eventually.of_forall fun _ x=>False.elim (he x)
lemma cash_viz {Z:∀ w,Dart G (n w)}{r:W→PathData G} (hx:∀ w,(Z w).Sound (r w) p)(h : Saving F Z u d e)(ε:ℝ)(hε:0<ε)(ht:∀ i,i≤4→ 2 ≤ i→ e i<ε): ∀ᶠ w in F,Viz (Z w) p (r w) u (fun i=>d i+1) (fun _=>ε) ε:=by
 have hD (i): d i<d i+1:=lt_add_one _
 filter_upwards [eventually_all.mpr (fun a=> eventually_all.mpr fun b=> cash_ear (n:=n) (J:=fun w x=>ballX ((Z w).J a b x)) (h.heart a b) (e:=fun i=>d i+1) (fun i _ _=> hD _)), eventually_all.mpr (fun a=> cash_ear (n:=n) (J:=fun w x=>bottom ((Z w).Y a x)) (h.palm a) (e:=fun i=>d i+1) (fun i _ _=>hD _)), eventually_all.mpr (fun a=> cash_ear (n:=n) (J:=fun w x=>ballX ((Z w).E a x)) (h.plum a) (e:=fun _=>ε) ht), eventually_all.mpr (fun a=> cash_ear (n:=n) (J:=fun w x=>ballX ((Z w).Q a x)) (h.plumQ a) (e:=fun i=>d i+1) (fun i _ _=>hD _)), eventually_all.mpr (fun a=>eventually_all.mpr fun b=>eventually_all.mpr fun i=> cash_ear (n:=n) (J:=fun w x=>ballX ((Z w).twist a b i x)) (h.mint a b i) (e:=fun i=>d i+1) (fun i _ _=>hD i)), eventually_all.mpr (fun a=> eventually_all.mpr fun b=> cash_tip (J:=fun w x=>ballX ((Z w).J a b x)) (h.ox a b) ε hε), eventually_all.mpr (fun a=>cash_tip (J:=fun w x=>bottom ((Z w).Y a x)) (h.orb a) ε hε)] with w Z K Y E v h g; exact ⟨hx w,Z,K,Y,E,v,h,g⟩

variable {M:Metals G}{D:Rolls M.p}{A: Alloy M D} (Vigil':Vigil A.B.a)(B:Bolt A)

set_option quotPrecheck false
include B Vigil'
theorem treasury : ∀ᶠ k:ℕ in atTop,∀ (ε:ℝ),0 < ε→∀ (F:Filter W)(N p:W→ℕ), Tendsto N F atTop→(∀ j,Tendsto (fun w=> (A.B.a.S.side j (p w)).val) F atTop) →∀ᶠ w in F, ∃ K:Dart G (A.B.a.S.side k (p w)),let Z:= (Issue.trail B).rep (N w) (p w) k; let x:=A.B.a.clock.hatBeta k; Viz K Z.clip Z.path (east x) (fun i=>reed x i+1) (fun _=>ε) ε:=by
 obtain ⟨b,h⟩:= eventually_atTop.mp Vigil'; refine (eventually_ge_atTop b).mono (fun j hj ε hε F N p hN hp=>?_)
 let f:= A.B.a.clock.hatBeta j
 obtain ⟨i,hi⟩ :∃ i:ℕ,∀ n,n≤4→2 ≤ n→vista (i+1) f n < ε:=by
    have h(i:ℕ): Tendsto (fun x:ℕ=> vista (x+1) f i) atTop (𝓝 0):=by  have ht:= (tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ (1:ℝ)/2 by norm_num) (by norm_num)|>.mul_const (1/2)|>.mul_const (reed f i)); simpa only[vista,pow_succ,zero_mul] using ht
    have he(i:ℕ):= (h i).eventually (gt_mem_nhds hε)
    exact ((show ∀ᶠ v:ℕ in atTop,∀ k,k≤4→2 ≤ k→vista (v+1) f k < ε from (by filter_upwards [he 2,he 3,he 4] with v ht hY hV k hk hi; interval_cases k<;> assumption))).exists
 let U:={w:W// j+(i+1)<N w}
 let K:= comap (Subtype.val:U→ W) F
 have hs:Tendsto (Subtype.val:U→W) K F:=tendsto_comap
 obtain ⟨Z,hZ,hS⟩:= through A (N ∘ Subtype.val) (p ∘ (Subtype.val:U→W))  Vigil' K (fun i=> (hp i).comp hs) j i (fun k hk=>h k (le_trans hj hk)) (fun u=>u.property)
 have he := cash_viz hZ hS ε hε hi
 have hq:= eventually_comap.mp he
 filter_upwards [hq, hN.eventually (eventually_gt_atTop (j+(i+1)))] with w hw ht
 let k:U:=⟨w,ht⟩; refine ⟨Z k,?_⟩
 have hi : j ≤ N w:= by omega
 intro X Y' ; have hp : X.clip=((Issue.trail B).levels.params j).clip:= (B.choice.represents (N w) (p w) j hi).clip
 rw [hp]; have hv:X.path=A.B.kin.path (N w) j:=by have hx:=((B.sticks (N w) (p w)).prices j (Nat.zero_le _) hi).1.path; rw [A.B.bases] at hx; exact hx
 rw [hv]; exact hw k rfl
end YM.Trace.Perfect
