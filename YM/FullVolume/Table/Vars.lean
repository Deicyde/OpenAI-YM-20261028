import YM.FullVolume.Table.Tabs
/-!
# Representatives per common permutation set
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Urns
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration RG.Shoot
open Push.PriceCompiler Push.AbsoluteSums Progress.DirectedRecipe Time UVNext.CouplingReset Ovens Ovens.Pipes
open PhysicalNext.Repeat.Apse PhysicalNext.Repeat.Jams
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge}{c:Side} {S:Price G c}
namespace Show
variable {a b:Show S}{u:Emote}{s:Signed}{B:Site c}
lemma turn_sub (h:amid u a.proper s B)(h':amid u b.proper s B): amid u (a-b|>.proper) s B:= by
  obtain ⟨f,hf,he⟩:= h; obtain ⟨g,hg,hθ⟩:= h'
  refine ⟨⟨f.ep,f.kp,f.reg_site, f.reg_support,f.forced_support,f.forced_inventory,f.forced_tests,fun i x=> ?_,fun i x=>?_⟩,hf,he⟩
  · exact congr_arg₂ (·-·) (f.valuesE i x) ((show g.ep=f.ep from hg.trans hf.symm) ▸ (g.valuesE i x))
  exact congr_arg₂ (·-·) (f.valuesK i x) ((show g.kp=f.kp from hθ.trans he.symm) ▸ (g.valuesK i x))
lemma turn_scale (p:ℝ) (h:amid u a.proper s B):amid u (p • a|>.proper) s B:= by obtain ⟨x,h,hx⟩:=h; exact ⟨⟨_,_,x.reg_site,x.reg_support,x.forced_support,x.forced_inventory,x.forced_tests,fun i U=> congr_arg (fun u:ℝ=>p*u) (x.valuesE i U),fun i U=>congr_arg (fun u:ℝ=>p*u) (x.valuesK i U)⟩,h,hx⟩
end Show
abbrev Team (S:Price G c):= {f: Signed→ Site c→ Emote // ∀ s v, amid (f s v) ((0:Show S).proper) s v}

def Home (t: Team S): Submodule ℝ (Show S) where
  carrier:= {a:Show S|∀ s b, amid (t.val s b) a.proper s b}
  zero_mem':= t.property
  add_mem' {x} {y} hx hy:=by
    intro s b; rw [show x+y=x- (-1:ℝ) • y from (by simp)]; exact Show.turn_sub (hx ..) (Show.turn_scale (-1) (hy ..))
  smul_mem' x y h:= fun s b=>Show.turn_scale x (h s b)
-- Print Layout exactly. note ambient topology includes off-mask germ hession at boundary, not point off mask.
abbrev Member (t:Team S) := Home t
variable {T:Team S} {v:ℝ}
def observe (t:Team S)(f:Home t):=f.val.proper
lemma qualifies (f:Home T)(hv:‖f‖ ≤ v): let A:= observe T f; Activities.Valid A S.p (v*S.b) (v*S.k):=by
  intro A; obtain ⟨hr,hk,hA,h⟩:= (Show.budget f.val v).mp (show ‖f.val‖≤ v from hv); exact ⟨hr,hk,fun s b=> ⟨(f.property s b).choose⟩,hA,h⟩
-- canonical injection. Holds even if nonseparable at labels.
lemma form {U : Activities G c} (h:U.reg=(layout G c S.p).reg)(hp:U.forced=(layout G c S.p).hard): issue S.p (U.E,U.K)=U:= by cases U; unfold issue Listing.read; congr; exact h.symm; exact hp.symm
lemma corresponds (T:Team S) (U:Activities G c) {a b:ℝ}(h:U.reg=(layout G c S.p).reg)(hp:U.forced=(layout G c S.p).hard)(he: U.Valid S.p a b) (ht:∀ s v, amid (T.val s v) U s v): ∃ x:Home T, observe T x=U:=by
   have hb : Cash S.p (U.E,U.K) a b:= by unfold Cash; rw [form h hp]; exact ⟨he.regular,he.forced,he.boundE,he.boundK⟩
   let X : arena S:=⟨_,a,b,hb⟩; let v:= (Show.peek (S:=S)).symm X
   have hx : v.proper=U:= form h hp
   exact ⟨⟨v, fun s b=> hx ▸ ht s b⟩,hx⟩
-- derive Rebar in completion from coupons.
section ray
open FullVolume.Ray UniformSpace
variable {q r b:ℝ}{w:Rung} (F:sun→ Home T)
lemma eats (hw : Stripe w q r)(hE:Acquittal (drawer G c).reg S.p (fun i=> (observe T (F i)).E) q b)(hv:league (fun i=> ((layout G c S.p).hard i).support) S.p.B (fun i=> (observe T (F i)).K) S.p.supportExponent q v)
   {a:ℝ}(h : b ≤ a*S.b)(hi:v≤a*S.k): ‖mix w F‖ ≤ r*a:=by
  let Y:= mix w F; change ‖Y.val‖≤ r*a; apply (Show.budget ..).mpr
  let X:= Show.proper Y.val; have hx : X=observe T Y:=rfl
  have hf (i): X.E i=mix w (fun x=> (observe T (F x)).E i):= by
    change ((Show.peek ((Home T).subtype _)).val.1 i)= _
    unfold mix; rw [map_sum,map_sum, Submodule.coe_sum, Prod.fst_sum, Finset.sum_apply]; simp_rw [map_smul]; rfl
  have hk i:X.K i=mix w (fun x=>(observe T (F x)).K i):= by
    change ((Show.peek ((Home T).subtype _)).val.2 i)= _
    unfold mix; rw [map_sum,map_sum, Submodule.coe_sum, Prod.snd_sum, Finset.sum_apply]; simp_rw [map_smul]; rfl
  obtain ⟨u,hU,hK⟩:= hE.stars w r hw
  obtain ⟨p,hp,hX⟩:= hv; have he:= rate_iff (f:=Show.peek (mix w F).val)|>.mp le_rfl
  have ht:= stripe_pos hw
  refine ⟨he.1, he.2.1,⟨u,fun i=>?_,fun i=>budget_loosen (hU i) ((mul_le_mul_of_nonneg_left h ht).trans_eq (mul_assoc r a S.b).symm)⟩, ?_⟩
  · change S.p.supBounds _ _ (X.E i) _; rw [hf]; have hu:=(hK i).2; rw [mix_eval] at hu; exact hu
  have hP i:0≤r*p i:= mul_nonneg ht (hX i 1|>.nonneg)
  refine ⟨fun i=>r*p i,fun i=>⟨hP i,fun V=>?_⟩,fun i=>?_⟩
  · change ‖X.K i V‖ ≤ _; rw [hk,mix_eval]; exact mix_d _ hw (hX i V)
  apply budget_loosen (C:=r*v) ?_ ((mul_le_mul_of_nonneg_left hi ht).trans_eq (mul_assoc r a S.k).symm)
  convert budget_scale ht (hp i) using 2 with i; unfold BudgetPoint.mass; dsimp only [observe,issue,Listing.read]; split <;> ring
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
lemma regs_map_eq {E:Type} [SeminormedAddCommGroup E] [NormedSpace ℝ E](w:Rung)(X:sun→E): mix w (fun i=> ((X i):UniformSpace.Completion E))=↑(mix w X):=by
  let T:=UniformSpace.Completion.toComplL (𝕜:=ℝ) (E:=E); change _=T (mix w X); unfold mix; rw [map_sum]; simp_rw [map_smul]; rfl
lemma witness (q b:ℝ)(hq:1≤q)(h:∀ w r,Stripe w q r→‖mix w F‖≤ r*b): Rebar q (phraseS (fun i=>((F i):Completion (Home T)))) b:= by
  have ht:= h 0 1 (fun i=> by simp [FullVolume.Ray.trace]); rw [one_mul] at ht
  exact ⟨hq,(norm_nonneg _).trans ht,fun w v he=>by rw [mix_made, regs_map_eq,Completion.norm_coe]; exact h w v he⟩
end ray
end YM.FullVolume.Urns
