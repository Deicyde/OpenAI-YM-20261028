import YM.RG08.Flint.Drive

/-! # Secondary Ward estimates, no finite periods. Speed d=1 provides
absolute-price source cancellation for all lower order via previous costs.
Distinguish nonlinear coefficient Ward from exact rente. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Flint
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Skiff Trickle
open Room Gallery Camera MvPolynomial Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary
open scoped Classical ContDiff BigOperators Topology PowerSeries ENNReal
variable {I J:Type}{G:Gauge}{n l p e d:ℕ}{C δ a σ B:ℝ}{w:G.El}{h:0<σ}
variable {X:Ed G Cover→ℝ}{U:Nd G Cover→ℝ}{M:GrainS (Ed G Cover)}

lemma grad_height (i:Ed G Cover): length (i.1+step (Quarry.back i.2.1))≤abroad i+1:= (length_add ..).trans_eq (by rw [length_step];rfl)
lemma grad_bearing (he:Bearing (stance G.ColorIndex) p δ a U)(h0:0≤δ)(hq:δ≤1):Bearing (stance (Loc G 1)) p δ ((hustle p 1 1+1)*a) (grad U):=by
 have hz:1 ≤ hustle p 1 1:=one_le_hustle p zero_le_one zero_le_one
 refine ⟨mul_nonneg (by linarith only [hz]) he.1,fun i=>?_⟩
 let u:Nd G Cover:= (i.1+step (Quarry.back i.2.1),i.2.2)
 have hf:=abroad_nn i
 apply (abs_sub _ _).trans ((add_le_add (he.2 u) (he.2 (i.1,i.2.2))).trans ?_)
 change a*hustle p δ (length u.1) + a*hustle p δ (abroad i) ≤ (hustle p 1 1 + 1)*a*hustle p δ (abroad i)
 have hx:hustle p δ (length u.1)≤ hustle p δ (abroad i)*hustle p 1 1:=by
    apply (hustle_in h0 (abroad_nn u) (grad_height i)).trans
    apply (hustle_plus h0 hf (show (0:ℝ)≤1 by norm_num)).trans
    apply mul_le_mul_of_nonneg_left _ (hustle_nn p _ hf)
    unfold hustle;rw [mul_one,mul_one]; gcongr
 linarith only [mul_le_mul_of_nonneg_left hx he.1]

-- all slots jointly general V,U; for grad one slot isolate.
private def capV (u : Fin n→ℝ):ℝ:=∑ j,|u j|
lemma capV_nn (u: Fin n→ℝ):0≤capV u:=sum_nonneg fun _ _=>abs_nonneg _
private theorem boost (G:Gauge)(l e n p:ℕ)(σ δ:ℝ)(hσ:0<σ)(hδ:0≤δ)(hδ':δ≤1)(hz:(↑((e+1)*(l+e)):ℝ)*δ≤σ/2)(hR:n≤l+e):∃ D:ℝ,0≤D ∧ ∀ (X:Fin n→Ed G Cover→ℝ)(U:Fin n→Nd G Cover→ℝ),
 (∀ i,Bearing (stance (Loc G 1)) p δ 1 (X i)) → (∀ i,Bearing (stance G.ColorIndex) p δ 1 (U i)) →
 (∀ i,Fenced (X i)) → (∀ i,Fenced (U i))→ ∀ (M:GrainS (Ed G Cover))(d:ℕ)(B T:ℝ)(f:Pearl),Calls l M → Permit d l M→0≤B→0≤T→(∀ i<e,∀ k≤l+i,Sings (stance _) d hσ (M i k) B)→(∀ k≤l+e,Sings (stance _) d hσ (M e k) T)→
 |sonic (M e n) f (fun i=>X i+grad (U i))-sonic (M e n) f X| ≤ D*B*beam d hσ f:=by
 let W(u:Fin n→ℝ):=junior G 1 p e l (capV u) σ
 obtain ⟨C,hC,H⟩:=septet W hR id
 refine ⟨C,hC,fun X U hX hU hw hy M d B T f he hu hB hT hM hE=>?_⟩
 let Y(i:Fin n):=X i+grad (U i)
 let F(k:ℕ):Flake k (Fin n):= modal (M e k) f Y-modal (M e k) f X
 have ha (k):Lyrics (M e k):=(hu.price e k).1 -- price = Lyrics? 
 have hf (k):Forms.Sym (during f (M e k)):=hu.fine f e k
 have hA (k)(V:Fin n→Ed G Cover→ℝ):Forms.Sym (modal (M e k) f V):= modal_sym _ (hf k)
 have hb(k):Forms.Sym (F k):=fun s=>funext fun i=> congrArg₂ (fun x y:ℝ=>x-y) (congrFun (hA k Y s) i) (congrFun (hA k X s) i)
 rw [mul_assoc]
 change |F n id| ≤ _
 apply H _ F (mul_nonneg hB (beam_nn ..)) (fun i _=>hb i);intro u
 let V:Ed G Cover→ℝ :=∑ i:Fin n,u i • X i; let Q:Nd G Cover→ℝ :=∑ i:Fin n,u i • U i
 have hX1:Bearing (stance (Loc G 1)) p δ (capV u) V:=by
    have hx:=Bearing.sum Finset.univ  (fun i (_:i∈(Finset.univ:Finset (Fin n)))=>(hX i).smul (u i)); simpa [capV] using hx
 have hU1:Bearing (stance G.ColorIndex) p δ (capV u) Q:=by have hx:=Bearing.sum Finset.univ (fun i (_:i∈(Finset.univ:Finset (Fin n)))=>(hU i).smul (u i)); simpa [capV] using hx
 have hV:Fenced V:=Fenced.sum univ _ (fun i _=>(hw i).smul _)
 have hQ:Fenced Q:=Fenced.sum univ _ (fun i _=>(hy i).smul _)
 refine LE.le.trans (b:=|(∑ i∈range (l+e+1), sonic (M e i) f (fun _=>leanTag V Q 1))-(∑ i∈range (l+e+1), sonic (M e i) f (fun _=>V))|) ?_ (ward_lower hδ hδ' hz hX1 hU1 he hu f hV hQ (1:G.El) hB hM)
 apply Eq.le;congr 1;rw [←sum_sub_distrib];apply sum_congr rfl;intro k hk
 have hK:k≤l+e:=by simp only [mem_range] at hk;omega
 have hK':(k:ℝ)*δ≤σ/2:= (mul_le_mul_of_nonneg_right (by exact_mod_cast hK.trans (Nat.le_mul_of_pos_left (l+e) (by omega))) hδ).trans hz
 have hY(i):Bearing (stance (Loc G 1)) p δ (1+(hustle p 1 1+1)*1) (Y i):= (hX i).add (grad_bearing (hU i) hδ hδ')
 have hl:leanTag V Q (1:G.El)=∑ i:Fin n,u i •Y i:=by
    change settle 1 (V+grad Q)=_;rw [settle_one];funext v;unfold Y; rw [Pi.add_apply,grad]
    unfold V Q; rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,←sum_sub_distrib,←sum_add_distrib];apply sum_congr rfl;intro i _
    simp_rw [Pi.smul_apply,smul_eq_mul,Pi.add_apply];unfold grad;ring
 rw [hl, modal_read (n:=k) f (ha k) (hE k hK) hT u _ hδ hK' hY, modal_read f (ha k) (hE k hK) hT u _ hδ hK' hX,parley_street,parley_street,←sum_sub_distrib]
 apply sum_congr rfl;intro i _; exact sub_mul _ _ _

private def clipper (s:Finset I)(X:I→ℝ):I→ℝ:=fun i=> if i∈s then X i else 0
private lemma clipper_f (s:Finset I)(X:I→ℝ):Fenced (clipper s X):=⟨s,fun _ hi=>if_neg hi⟩
private lemma clipper_b {L:Jetty.Loom I}{X:I→ℝ}(s:Finset I)(h:Bearing L p δ a X):Bearing L p δ a (clipper s X):=by
 refine ⟨h.1,fun i=>?_⟩;unfold clipper;split;exact h.2 i; rw [abs_zero];exact mul_nonneg h.1 (hustle_nn _ _ (L.nn _))
/-- Full replacement of any list of growing probe directions. Includes stencil-point
applications. Controlled on exact beam-compliant tests as a dual (mom cost supplied separately).
Only lower order costs survive, irrespective of number of gradients!
D is announced before L (the additional T only needs finiteness for HT, drops away at lift).
Can ask widths δ decreasing via monotonicity or use largest δ possible in seq.
-/
theorem spark (G:Gauge)(l e n p:ℕ)(σ δ:ℝ)(hσ:0<σ)(hδ:0≤δ)(hδ':δ≤1)(hz:(↑((e+1)*(l+e)):ℝ)*δ≤σ/2)(hR:n≤l+e):∃ D:ℝ,0≤D ∧ ∀ (X:Fin n→Ed G Cover→ℝ)(U:Fin n→Nd G Cover→ℝ),
 (∀ i,Bearing (stance (Loc G 1)) p δ 1 (X i)) → (∀ i,Bearing (stance G.ColorIndex) p δ 1 (U i)) →
 ∀ (M:GrainS (Ed G Cover))(d:ℕ)(B T:ℝ)(f:Pearl),Calls l M → Permit d l M→0≤B→0≤T→(∀ i<e,∀ k≤l+i,Sings (stance _) d hσ (M i k) B)→(∀ k≤l+e,Sings (stance _) d hσ (M e k) T)→
 |sonic (M e n) f (fun i=>X i+grad (U i))-sonic (M e n) f X| ≤ D*B*beam d hσ f:=by
 obtain ⟨D,hD,H⟩:= boost G l e n p σ δ hσ hδ hδ' hz hR
 refine ⟨D,hD,fun X U hX hU M d B T f he hu hB hT hM hV=>?_⟩
 let χ:=Finset (Ed G Cover) × Finset (Nd G Cover); let Y(s:χ)(x:Fin n):=clipper s.1 (X x); let V(s:χ)(x:Fin n):=clipper s.2 (U x)
 have hx(s i):Bearing (stance _) p δ 1 (Y s i):=clipper_b _ (hX i); have hv(s i):Bearing (stance _) p δ 1 (V s i):= clipper_b _ (hU i)
 have hd(s:χ): |sonic (M e n) f (fun i=>Y s i+grad (V s i))-sonic (M e n) f (Y s)| ≤ D*B*beam d hσ f:= H _ _ (hx s) (hv s) (fun _=>clipper_f ..) (fun _=>clipper_f ..) _ _ _ _ _ he hu hB hT hM hV
 have hh(i j): Tendsto (fun s=>Y s i j) atTop (𝓝 (X i j)):=Filter.EventuallyEq.tendsto (by filter_upwards [eventually_ge_atTop (({j},∅):χ)] with s hs;unfold Y clipper;rw [if_pos (hs.1 (mem_singleton_self _))])
 have ht(i j): Tendsto (fun s=>V s i j) atTop (𝓝 (U i j)):=Filter.EventuallyEq.tendsto (by filter_upwards [eventually_ge_atTop ((∅,{j}):χ)] with s hs;unfold V clipper;rw [if_pos (hs.2 (mem_singleton_self _))])
 have Hn:(n:ℝ)*δ≤σ/2:=(mul_le_mul_of_nonneg_right (by exact_mod_cast hR.trans (Nat.le_mul_of_pos_left (l+e) (by omega))) hδ).trans hz
 have hr:=sonic_turn (l:=atTop) f ((hu.price e n).1) (hV n hR) hT (Y:=fun i=>X i+grad (U i)) (X:=fun s i=>Y s i+grad (V s i)) (fun i j=>(hh i j).add ((ht i _).sub (ht i _))) hδ Hn (a:=fun _=>1+(hustle p 1 1+1)*1) (fun s i=>(hx ..).add (grad_bearing (hv s i) hδ hδ'))
 have hg:=sonic_turn (l:=atTop) f ((hu.price e n).1) (hV n hR) hT hh hδ Hn (a:=fun _=>1) hx
 exact le_of_tendsto (hr.sub hg|>.abs) (.of_forall hd)
end YM.RG08.Flint
