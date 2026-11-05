import YM.UVExtension.Wren.Bolo
import YM.UVExtension.Steady.Twins
/-!
 Transit in fixed label spaces. Currency-neutral AFTER volume fixed and masks
 and leg lengths fixed. Countable generation children only where Haar.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Steady
open Filter Function Metric Set RG Lattice Push.AbsoluteSums Finset
open scoped BigOperators Topology ContDiff Classical
variable {ι κ π θ : Type*}{v:Filter ι} {X Z: Type*} [NormedAddCommGroup Z] {f g:ι→ X→ Z}
-- "bounded Cauchy" in a single probe's full evaluation. all i-bounds separated.
structure Tune (v:Filter ι)(f:ι→X→Z):Prop where
    price : ∃ u:ℝ,∀ᶠ n in v,∀ x, ‖f n x‖ ≤ u
    uv (ε:ℝ) (he:0<ε): ∀ᶠ n in v×ˢv,∀ x, ‖f n.1 x-f n.2 x‖≤ε
variable {A:κ→Type*}{R Q:(n:ι)→(x:κ)→(a:A x)→Z}
structure Transit (v:Filter ι)(R:(n:ι)→(x:κ)→(a:A x)→Z):Prop where
    rain: ∃ f,Swift v f ∧ ∀ᶠ i in v,∀ j x, ‖R i j x‖ ≤ f i j
    meters (x:κ): Tune v (fun n a=> R n x a)
namespace Tune
lemma leaf (h:Tune v f){qq:Filter θ}(aS:θ→Bool→ι)(he:∀ b,Tendsto (fun i=>aS i b) qq v)(U:θ→X): Together qq (fun i b=> f (aS i b) (U i)):=by
   obtain ⟨y,hy⟩:= h.price; exact Together.of_cap _ ⟨y,(eventually_all.mpr (fun b=> (he b).eventually hy)).mono fun n hn b=> hn b (U n)⟩ fun ε hε=> ((he true).prodMk (he false)|>.eventually (h.uv ε hε)).mono fun i hi=> hi (U i)
-- contrapositive shoe. vacuous if no inputs
lemma unanimously (X : Type*) (p:ι→X→Prop)(w:Filter ι) (h:∀ V:ι→ X,∀ᶠ n in w,p n (V n)): ∀ᶠ n in w, ∀ x, p n x:=by
   cases isEmpty_or_nonempty X with
   | inl u => exact Eventually.of_forall (fun n t=> isEmptyElim t)
   | inr u =>
      let f (i:ι) := if h:∃ x : X, ¬p i x then Classical.choose h else u.some
      filter_upwards [h f] with i hi x; by_contra hx; have hh:∃ v,¬p i v:= ⟨_,hx⟩; unfold f at hi; rw [dif_pos hh] at hi; exact Classical.choose_spec hh hi
lemma spans (p : ∃ u:ℝ,∀ᶠ n in v,∀ x,‖f n x‖≤u)(h:∀ t:ι × ι → X,Together (v×ˢv) (fun n b=> if b then f n.1 (t n) else f n.2 (t n))):Tune v f:=by
    refine ⟨p,fun ε he=> unanimously _ _ _ (fun V=> ?_)⟩; exact (h V).cap ε he
lemma switch (h:Tune v f)(he:∀ᶠ n in v,f n=g n):Tune v g:=by
   obtain ⟨r,hr⟩:=h.price
   refine ⟨⟨r,(hr.and he).mono fun n hn=> hn.2 ▸ hn.1⟩,fun ε hε=>?_⟩; filter_upwards [h.uv ε hε, (tendsto_fst.eventually he).and (tendsto_snd.eventually he)] with n hn hx z; rw [← hx.1,←hx.2]; exact hn z
lemma nil : Tune v (fun (_:ι)(_ : X)=> (0:Z)):= ⟨⟨0,by simp⟩, fun ε he=> by simp [he.le]⟩
lemma cues (h:Tune v f) (w:π→ X): Tune v (fun n i=> f n (w i)):=by
   obtain ⟨r,hp⟩:= h.price; exact ⟨⟨r,hp.mono fun n hp x=> hp _⟩,fun ε he=> (h.uv ε he).mono fun n hp x=> hp _⟩
lemma constant (a:ι→Z)(u:Z)(h:Tendsto a v (𝓝 u)): Tune v (fun n (_:X)=>a n):=by
  refine ⟨⟨1+‖u‖,(h.norm.eventually_le_const (by simp)).mono fun n hn x=> hn⟩,fun ε he=>?_⟩
  have ht:=h.eventually (ball_mem_nhds u (half_pos he)); filter_upwards [(tendsto_fst.eventually ht).and (tendsto_snd.eventually ht)] with n h x; rw [← dist_eq_norm]; refine (dist_triangle (a n.1) u (a n.2)).trans ?_; rw [dist_comm u]; exact (add_le_add (mem_ball.mp h.1).le (mem_ball.mp h.2).le).trans_eq (add_halves ε)
lemma add (h:Tune v f)(p:Tune v g): Tune v (fun n x=> f n x+g n x):=by
  obtain ⟨k,hk⟩:=h.price; obtain ⟨s,hs⟩:=p.price
  refine ⟨⟨k+s,(hk.and hs).mono fun n hh x=> (norm_add_le ..).trans (add_le_add (hh.1 x) (hh.2 x))⟩,fun ε he=>?_⟩; filter_upwards [h.uv _ (half_pos he),p.uv _ (half_pos he)] with n hx hk x; simp_rw [add_sub_add_comm]; exact (norm_add_le ..).trans ((add_le_add (hx x) (hk x)).trans_eq (add_halves ε))
lemma sub (h:Tune v f)(p:Tune v g): Tune v (fun n x=> f n x-g n x):=by
  have hp:Tune v (fun n x=> -(g n x)):= by
    obtain ⟨s,hs⟩:= p.price; refine ⟨⟨_,hs.mono (fun i h x=> by rw [norm_neg]; exact h x)⟩,fun ε he=> ?_⟩; filter_upwards [p.uv ε he] with n hn x; rw [neg_sub_neg,norm_sub_rev]; exact hn x
  simpa only [sub_eq_add_neg] using h.add hp
lemma term (s: Finset κ)(V:κ→ι→ X→Z)(h:∀ i∈s,Tune v (V i)):Tune v (fun n x=> ∑ i∈s,V i n x):=by
   induction s using Finset.induction with
   | empty => simp only [sum_empty]; exact nil
   | insert i s hi hh=> simp_rw [sum_insert hi]; exact (h _ (mem_insert_self ..)).add (hh fun k hk=> h _ (mem_insert_of_mem hk))
lemma mask (h:Tune v f)(w:X→Prop)[DecidablePred w]: Tune v (fun n x=> if w x then f n x else 0) :=by
   obtain ⟨r,hr⟩:=h.price; refine ⟨⟨max r 0,hr.mono fun i hh x=>?_⟩,fun ε he=>?_⟩
   · split; exact (hh x).trans (le_max_left ..); rw [norm_zero]; exact le_max_right ..
   filter_upwards [h.uv ε he] with n hn x; split; exact hn x; rw [sub_zero,norm_zero]; exact he.le
lemma prod {Y:Type*}[NormedAddCommGroup Y]{g:ι→X→Y}(h:Tune v f)(p:Tune v g): Tune v (fun n x=> (f n x,g n x)):=by
   obtain ⟨r,hr⟩:= h.price; obtain ⟨s,hs⟩:=p.price
   refine ⟨⟨max r s,(hr.and hs).mono fun n hp x=>max_le_max (hp.1 _) (hp.2 _)⟩,fun ε he=>?_⟩
   filter_upwards [h.uv ε he,p.uv ε he] with n hn hh x; exact max_le (hn x) (hh x)
lemma cont [ProperSpace Z](h:Tune v f){Y:Type*}[NormedAddCommGroup Y]{F:Z→Y}(hc:Continuous F): Tune v (fun n x=> F (f n x)):=by
    obtain ⟨r,hr⟩:= h.price; obtain ⟨y,hy⟩:= ((isCompact_closedBall 0 r).image hc).isBounded.exists_norm_le
    refine spans ⟨y,hr.mono (fun i hh x=> ?_)⟩ fun V=>?_
    · exact hy _ (Set.mem_image_of_mem F (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hh x)))
    let t (i:ι×ι)(b:Bool): ι:= if b then i.1 else i.2; refine ((h.leaf t (fun b=> by cases b <;> first | exact tendsto_snd| exact tendsto_fst) V).continuous hc).shimmy (by filter_upwards with i; ext1 b; cases b <;> rfl)
lemma mul {f g:ι→X→ℝ}(p:Tune v f)(h:Tune v g): Tune v (fun n x=> f n x*g n x):= (p.prod h).cont (F:=fun (x:ℝ×ℝ)=> x.1*x.2) (by fun_prop)
end Tune
namespace Transit
lemma fade (h:Transit v R)(he:∀ᶠ n in v,∀ i, R n i=Q n i): Transit v Q:= by
   obtain ⟨f,hf,hp⟩:=h.rain; exact ⟨⟨f,hf,(he.and hp).mono fun n h i=> h.1 i▸h.2 i⟩,fun j=> (h.meters j).switch (he.mono fun n hn=> hn j)⟩
lemma drought (h:Transit v R): ∀ ε:ℝ, 0 < ε → ∀ᶠ n in v×ˢv,∃ c:κ→ ℝ, SumBudget c ε ∧ ∀ j x, ‖R n.1 j x -R n.2 j x‖ ≤ c j:=by
   obtain ⟨f,hf,hV⟩:= h.rain; intro ε he; let E:= ε/3; have hp:0<E:=by unfold E; positivity
   obtain ⟨s,hs⟩:=hf.drops E hp; let b i:κ→ ℝ:= fun j=> if j∈s then 0 else f i j
   let k:=E/(s.card+1); have hh:0<k:= by unfold k; positivity
   filter_upwards [(eventually_all_finset s).mpr (fun i _=> (h.meters i).uv _ hh), (tendsto_fst.eventually (hV.and hs)).and (tendsto_snd.eventually (hV.and hs))] with n hn hx
   let B (i:κ):=∑ j∈s,if j=i then k else 0; have hB:SumBudget B E:=by
       have hl:= budget_over s (fun i j : κ=> if i=j then k else 0) (fun _=> k) ?_; swap
       · intro i _; exact budget_of_sum (fun j=>by split; exact hh.le; exact le_rfl) (fun j=>by simp only [Finset.sum_ite_eq]; split <;> first | exact le_rfl| exact hh.le)
       rw [sum_const,nsmul_eq_mul] at hl; exact budget_loosen hl ((mul_le_mul_of_nonneg_right (show (s.card:ℝ) ≤ s.card+1 by linarith) hh.le).trans_eq (by unfold k; field_simp))
   let U:=fun i=> B i+b n.1 i+b n.2 i
   refine ⟨U,budget_loosen (budget_plus (budget_plus hB hx.1.2) hx.2.2) (by unfold E; linarith),fun i x=>?_⟩
   by_cases he:i∈s
   · simp only [U,b,B,sum_ite_eq',if_pos he,add_zero]; exact hn i he x
   simp only [U,b,B,sum_ite_eq',if_neg he,zero_add]; exact (norm_sub_le ..).trans (add_le_add (hx.1.1 i x) (hx.2.1 i x))
lemma includes [CompleteSpace Z]{A:κ→Type*}{R:ι→(x:κ)→A x→ Z} (p: Transit v R)(h: X→(x:κ)→A x) : Tune v (fun i u=>∑' j,R i j (h u j)) :=by
   obtain ⟨f,hf,hR⟩:= p.rain; obtain ⟨B,hb⟩:= hf.books
   have he : ∀ᶠ n in v,∀ u, Summable (fun j=> ‖R n j (h u j)‖) ∧ ‖∑' j,R n j (h u j)‖≤ B:= by
      filter_upwards [hb,hR] with n hn h u; refine let h:SumBudget _ _ :=budget_mono hn (fun _=> norm_nonneg _) (fun j=> h j _); ⟨h.2.1, (norm_tsum_le_tsum_norm h.2.1).trans h.2.2⟩
   refine ⟨⟨B,he.mono fun n hn x=> (hn x).2⟩,fun ε hε=>?_⟩
   filter_upwards [p.drought _ hε, (tendsto_fst.eventually he).and (tendsto_snd.eventually he)] with n hn hu x; obtain ⟨f,hf,hV⟩:=hn
   have hf':SumBudget (fun j=> ‖R n.1 j (h x j)-R n.2 j (h x j)‖) ε := budget_mono hf (fun j=> norm_nonneg _) (fun i=> hV i _)
   rw [← (hu.1 x).1.of_norm.tsum_sub (hu.2 x).1.of_norm]; exact (norm_tsum_le_tsum_norm hf'.2.1).trans hf'.2.2
lemma many (p:Transit v R)(a:π→ κ)(h:Injective a){Z:π→Type*}(b:∀ i,Z i→ A (a i)): Transit v (fun n x k=> R n (a x) (b x k)):=by
   obtain ⟨f,hf,hP⟩:=p.rain; exact ⟨⟨_,hf.letters a h,hP.mono fun n hn i x=> hn _ _⟩,fun i=> (p.meters _).cues _⟩
lemma zero : Transit v (fun (_:ι)(i:κ)(_ : A i)=> (0:Z)):= ⟨⟨fun _ _=>0, Swift.nil (fun i=>0) (show SumBudget _ 0 from (by simp [SumBudget])), Eventually.of_forall fun i j x=> norm_zero.le⟩, fun _=> Tune.nil⟩
lemma ready [Finite κ] (p:∀ x:κ,Tune v (R · x ·)): Transit v R:=by
   choose f hf using fun i=> (p i).price; let h:=eventually_all.mpr hf
   refine ⟨⟨fun _ i=>|f i|,Swift.sight (fun i=> ⟨_,h.mono (fun n hn=> ⟨abs_nonneg _,le_refl _⟩)⟩),h.mono fun n hn i k=> (hn i k).trans (le_abs_self _)⟩,p⟩
lemma together (p: Transit v R)(h:Transit v Q): Transit v (fun n i x=> R n i x+Q n i x):=by
    obtain ⟨f,hf,hR⟩:=p.rain; obtain ⟨q,hq,hQ⟩:=h.rain; exact ⟨⟨_,hf.plus hq,(hQ.and hR).mono fun n hn i k=> (norm_add_le ..).trans (add_le_add (hn.2 _ _) (hn.1 _ _))⟩,fun i=> (p.meters i).add (h.meters i)⟩
lemma shifts [Finite π] (p:Transit v R){Z:π×κ→Type*}(X : ∀ (i:π×κ),Z i → A i.2):Transit v (fun n i k=>R n i.2 (X i k)):=by
    obtain ⟨f,hf,hR⟩:=p.rain; let e (_:ι)(_ : π):=(1:ℝ); have he: Swift v e:=Swift.sight fun _=> ⟨1,Eventually.of_forall fun n=> ⟨zero_le_one,le_rfl⟩⟩
    refine ⟨⟨_,he.mixes hf,hR.mono fun n hn i k=>?_⟩,fun i=> (p.meters _).cues _⟩; unfold e; rw [one_mul]; exact hn i.2 (X i k)
lemma merge {R:ι→κ→ X→Z}{Q:ι→π→ X→ Z}(p:Transit v R)(h:Transit v Q): Transit v (fun n i=> Sum.elim (R n) (Q n) i) :=by
    obtain ⟨f,hf,hR⟩:=p.rain; obtain ⟨q,hq,hQ⟩:=h.rain; exact ⟨⟨_,hf.onion hq,(hR.and hQ).mono (fun n hn i=> match i with| Sum.inl i=> hn.1 i | .inr i=> hn.2 i)⟩,fun i=> match i with| Sum.inl i=>p.meters i| .inr i=> h.meters i⟩
lemma masks (p: Transit v R)(w:(x:κ)→A x→Prop)[∀ x,DecidablePred (w x)]: Transit v (fun n x y=> if w x y then R n x y else 0):=by
   obtain ⟨f,hf,hR⟩:=p.rain; obtain ⟨r,hr⟩:=hf.books; refine ⟨⟨_,hf,(hr.and hR).mono fun n hn x k=>?_⟩,fun x=> (p.meters _).mask _⟩; split; exact hn.2 x k; rw [norm_zero]; exact hn.1.1 _
lemma varying (p: Transit v R)(w:ι→κ→Prop)(W:κ→Prop)(hp:∀ i,∀ᶠ n in v,w n i=W i) [∀ n,DecidablePred (w n)] : Transit v (fun n x k=> if w n x then R n x k else 0):=by
    obtain ⟨f,hf,hR⟩:=p.rain; obtain ⟨r,hr⟩:=hf.books; refine ⟨⟨_,hf,(hr.and hR).mono fun n hn x k=>?_⟩,fun x=>?_⟩
    · split; exact hn.2 x k; rw [norm_zero]; exact hn.1.1 _
    by_cases hw:W x
    · apply (p.meters x).switch; filter_upwards [hp x] with i hi; simp [hi,hw]
    apply Tune.nil.switch; filter_upwards [hp x] with i hi; simp [hi,hw]
end Transit
end YM.UVExtension.Steady
