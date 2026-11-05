import YM.RG08.Vale.Pep
/-!
# Port on the top slot of rank j. Receives nothing below. Sailed weight
leading in position-polynomials **including address derivatives**.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Precision Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {S ξ Υ R A B z:ℝ} {d D m j r h:ℕ} {L c f:Side} {V:EnvelopeU D R G r}
variable {X:Cross L (Loc G 1) (Loc G 1)} {F:Labels.Frame G d}
lemma passPlus (h:Polished V)(x:Fin r→ Potential G)(t:Fin r→ℕ)(hp:∀ i,x i∈Place.rangeLt (Axis→G.Color) (t i))(p q:Exam D): pass V x (p+q)=pass V x p+pass V x q := by
  unfold pass wallet; simp only [plug,map_add,_root_.add_apply,Function.comp_apply,ContinuousLinearMap.apply_apply,add_mul]; exact Summable.tsum_add (pocketbook V h t x hp p) (pocketbook V h t x hp q)
lemma passSc (V:EnvelopeU D R G r)(x:Fin r→Potential G)(t:ℝ)(p:Exam D): pass V x (t•p)=t* pass V x p := by unfold pass wallet; simp [plug,mul_assoc,tsum_mul_left]
lemma pass_arity (x:Fin r→Potential G)(T:Fin r→ℝ)(g:Exam D) : pass V (fun i=> T i • x i) g=(∏ i,T i)*pass V x g := by
  unfold pass wallet; rw [←tsum_mul_left]; apply tsum_congr; intro j; unfold deckP; simp only [Pi.smul_apply,map_smul,smul_eq_mul, Finset.prod_mul_distrib]; ring
lemma pass_merge (h:Polished V)(z: Fin r→ℕ)(x y:Fin r→ Potential G)(ht:∀ i,x i∈Place.rangeLt (Axis→G.Color) (z i))(hp:∀ i,y i∈Place.rangeLt (Axis→G.Color) (z i))(g:Exam D):
    pass V (x+y) g=∑ s: Fin r→Bool,pass V (fun i=> if s i then x i else y i) g := by
  let A (i:Fin r) (s:Bool):Potential G := if s then x i else y i
  let f (s : Fin r→Bool)(b : Beads (Loc G 1) r):= plug g R (V b)*∏ i,deckP (A i (s i)) (b i)
  have he i s : A i s∈ Place.rangeLt (Axis→G.Color) (z i):= by unfold A; split_ifs; apply ht; apply hp
  have hs s: Summable (f s):= pocketbook V h _ _ (fun i=>he i _) g
  let B (i:Fin r)(s:Bool):= deckP (A i s)
  have hT (i:Fin r)(p:Fare G): deckP ((x+y) i) p=∑ s:Bool, B i s p:= by
    simp only [deckP,Pi.add_apply,map_add]; rw [Fintype.sum_bool]; rfl
  unfold pass wallet; change _= ∑ s,∑' i,f s i; rw [←Summable.tsum_finsetSum (fun i _=>hs i)]; apply tsum_congr; intro j; unfold f; simp_rw [hT]
  rw [← Finset.mul_sum]; congr 1; exact Fintype.prod_sum ..
lemma pass_fall (h : Polished V)(g:Abates V d)(z:Fin r→ℕ)(v w : Fin r→Place.Potential G)
    (hp:∀ i,0< z i)(hv:∀ i,v i∈ Place.rangeLt _ (z i))(hw:∀ i,w i-v i∈ Place.rangeLt _ (z i-1)) (φ:Cham) (hc:(∑ i,z i)+cashT φ≤d):
    pass V w (coinsT D φ)=pass V v (coinsT D φ) := by
  let b i:= w i-v i; have hh : w=v + b := by funext i; dsimp only [b,Pi.add_apply]; abel
  let U (j:Fin r→ Bool)i:= if j i then v i else b i
  rw [hh,pass_merge h z _ _ hv (fun i=> Place.grows _ (Nat.sub_le ..) (hw i))]; rw [sum_eq_single (fun _=>true)]
  · congr 1
  · intro i _ hi; have hx: ∃ j,i j=false:= by
      by_contra! he; exact hi (funext fun _=> Bool.eq_true_of_not_eq_false (he _))
    let a j:=if i j then z j else z j-1
    have he : ∑ j,a j <∑ j,z j:= sum_lt_sum (fun j _=> by unfold a; split <;> omega) (by obtain ⟨k,hk⟩:=hx; exact ⟨k,mem_univ _,by unfold a; rw [if_neg (by rw [hk]; simp)]; have :=hp k; omega⟩)
    exact g (U i) a (fun u=> by unfold U a; split; apply hv; apply hw) φ ((Nat.add_lt_add_right he _).trans_le hc)
  simp
lemma pass_just (u:Cham)(x:E4)(c:ℝ)(hV: Polished V)(z:Fin r→ℕ)(A:Fin r→Potential G)(he:∀ i, A i∈ rangeLt _ (z i)) (h:Abates V d)(ht:(∑ i,z i)+cashT u≤d):
    pass V A (Scores.Pages.roll x c (coinsT D u)) = c^(cashT u)*pass V A (coinsT D u) := by
  let t:=c^(cashT u); let U:=coinsT D u; let P:=Scores.Pages.roll x c U; let K:= P-t•U
  have hv : pass V A K=0 := by
    have heq: K.val∈ Place.rangeLt ℝ (cashT u):= roll_only ..
    cases hy:cashT u with
    | zero=> rw [hy,rangeLt,Submodule.mem_bot] at heq; rw [show K=0 from Subtype.ext heq]; simp [pass,wallet,plug]
    | succ n=>rw [hy] at heq; exact banner h hV z A he (by omega) K (passT heq)
  rw [show Scores.Pages.roll x c (coinsT D u)=K+t•U from Eq.symm (sub_add_cancel ..),passPlus hV A z he,hv,passSc,zero_add]
lemma spray_whole (K:Flight j m)(c:ℝ)(hc:0<c)(hv:4≤m): Whole (painted G (Carrier.linesOf K c)):=by
  obtain ⟨q,C,h,H⟩:= Carrier.stored K c hc hv; exact ⟨_,_,h,paint_budget H⟩
lemma halo_falls (h:1/2≤R)(K:Flight j m) (hv:0<S)(hp:4≤m)(A:Abates V d) (hV: Tidy V)(hC: Polished V)(p:Site K.L)(φ:Cham)(x:Fin r→Potential G)(a:Fin r→ℕ)(he:∀ i,x i∈rangeLt _ (a i))(hw:∀ i,a i≤ j)(ht:∀ i,0<a i)(hy:(∑ i,a i)+cashT φ≤ d):
    pass (halo p V (painted G (Carrier.linesOf K S))) x (coinsT D φ) = height K.L ((∑ i,a i)+cashT φ)* pass V x (coinsT D φ) := by
  choose W hP H hW using fun i=> translate_cost K S hv hp (hw i) p _ (he i)
  rw [halo_poly K.odd h (spray_whole K S hv hp) hV hC _ _ _ j (fun i=> Place.grows _ (hw i) (he i))]
  simp_rw [hW]
  let k:=Carrier.unitStep K.L
  change pass V W _= _
  let f i:= height K.L (a i) • x i; have hg i: f i ∈ rangeLt _ (a i):= Submodule.smul_mem _ _ (he i)
  rw [pass_just _ _ _ hC a W hP A hy, pass_fall hC A a f W ht hg H φ hy]; unfold f; rw [pass_arity]; unfold height Carrier.unitStep; rw [pow_add,prod_pow_eq_pow_sum]; ring

lemma rank_launch (R: Shale (Loc G 1) r)(h:Tidy R)(hp:Polished R)(v : Fin r→ Snap G d) :
    amount R d r v=(r.factorial:ℝ)* wallet R (fun i=>deckP (Place.sampled (v i))) := by
  rw [penny_amt h hp]; unfold vault; rw [sum_eq_single (.atomic r)]; swap
  · intro i _ he; unfold penny; rw [grant_else]; simp; exact fun hh=>he (Cases.finest i hh)
  swap; · simp
  change (r.factorial:ℝ)* wallet (grant r R) (fun i z=> iteratedFDeriv ℝ 1 (screenR G d z) 0 (v ∘ (OrderedFinpartition.atomic r).emb i))=_; rw [grant_self]; congr 1
  apply congr_arg (wallet R); funext i p
  let e:= Film.sampleIn (Place.seat p.1) (heap p).2 (G:=G) (d:=d)
  let A:= Place.logo ∘ e
  have ht : screenR G d p=(fun x=> scent p.2.2 (Place.logo (e x))):=rfl
  have he:= motionD e p.2.2 1 (fun _=> v i); rw [iteratedFDeriv_one_apply] at he; rw [ht,iteratedFDeriv_one_apply]
  refine he.trans ?_; rw [iteratedFDeriv_one_apply, Place.echoing]; simp [e,deckP,Place.sampled,Function.comp_apply, Film.sampleIn]

end YM.RG08.Vale
