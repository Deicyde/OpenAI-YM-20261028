import YM.UVExtension.Tide.Lagoon
import YM.UVExtension.Crown.Sides
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Tide
open Function Filter Set Lattice RG Push Spire
open Lamppost Metric SectorNext Hearth Pier MergeProof.Ribbons
open Swell
open scoped Topology BigOperators Classical ContDiff
variable {a b r s:ℝ}
-- saves/cuts - quantitative analyt interpolation at scaled J. Need large S only.
lemma saveR (u b:ℝ)(hb:0 ≤ b)(hu:0<u) (ha:0<a): ∃ t:ℝ,0<t ∧ t<a ∧ ∀ (i:ℝ),0≤ i → ∀ f:ℂ→ℂ,DifferentiableOn ℂ f (ball 0 a)→ (∀ z∈Metric.ball (0:ℂ) a,‖f z‖ ≤ Real.exp (b*i))→(∀ x:ℝ,|x|<a→‖f x‖ ≤ Real.exp (-u*i))→ ∀ z∈ball (0:ℂ) t, ‖f z‖ ≤ Real.exp (-(u/2)*i):=by
    let d:= a/5; have hd: 0<d:= by unfold d; positivity
    let t:= min d ((d*u)/(8*(b+u))); have ht:0<t:=by unfold t; positivity
    refine ⟨t,ht, (min_le_left ..).trans_lt (by unfold d; linarith),fun i hi f hf h hx z hz=>?_⟩
    let k:= (b+u)*i; have hk:0≤k:= by unfold k; positivity
    have he : Real.exp (b*i)=Real.exp (-u*i)*Real.exp k:=by rw [←Real.exp_add]; unfold k; ring_nf
    have hz₀:= (Complex.abs_im_le_norm z).trans (mem_ball_zero_iff.mp hz|>.le); have hr:= (mem_ball_zero_iff.mp hz).le.trans (min_le_left ..)
    refine (Sides.peak f (Real.exp_pos _).le hk ha hf (fun z h'=> (h z h').trans_eq he) hx z hd ?_ (hz₀.trans (min_le_left ..))).trans ?_
    · have hs: a=5*d:=by unfold d; ring
      linarith only [Complex.abs_re_le_norm z,hr,hs,hd]
    rw [←Real.exp_add]; apply Real.exp_monotone; have hp:=hz₀.trans (min_le_right ..); have hy:= (le_div_iff₀ (show 0<8*(b+u) by positivity)).mp hp
    have hx:4*(|z.im|/d)*k≤ u/2*i:= by
       apply le_trans (le_of_eq (show 4*(|z.im|/d)*k= (4*|z.im| *(b+u)*i)/d by unfold k; ring)); apply (div_le_iff₀ hd).mpr; linarith only [mul_le_mul_of_nonneg_right hy hi]
    linarith only [hx]
lemma rapid (S:Schedule) (u:ℝ)(hu:0<u): Summable (expS S (-u)):=by
   let f:= Real.exp (-u*Real.log 3); have hx:f<1:= Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hu) (Real.log_pos (by norm_num)))
   refine (summable_geometric_of_lt_one (Real.exp_pos _).le hx).of_nonneg_of_le (fun i=> (Real.exp_pos _).le) ?_
   intro i; unfold expS; rw [← Real.exp_nat_mul]; apply Real.exp_monotone; apply (mul_le_mul_of_nonpos_left (delay S i) (neg_nonpos.mpr hu.le)).trans (le_of_eq ?_); ring

-- strip-start shrink helper reduces Sail on REAL d parameters of different disk
lemma rescue (u b:ℝ)(ha:0<a)(hx:0<u)(hb:0≤b) (S:Schedule): ∃ s:ℝ, ∃ hs:0<s, ∃ hp:s ≤ a,∀ᶠ i in atTop,∀ f:Row a→ℂ,Sail (desk a ha) f (Real.exp (b*S.scale i)) → (∀ x:Row a, ‖f x‖ ≤Real.exp (-u*S.scale i))→ Sail (desk s hs) (fun x:Row s=> f ⟨x.val,x.property.trans_le hp⟩) (Real.exp (-(u/2)*S.scale i)):=by
   obtain ⟨s,hs,hp,H⟩:= saveR u b hb hx ha; refine ⟨s,hs,hp.le,?_⟩; filter_upwards [S.divergent.eventually_ge_atTop 0] with i hi f hf h; obtain ⟨g,hg,he,hV⟩:=hf
   have he' : DifferentiableOn ℂ g (ball 0 a):= hg _ id isOpen_ball (mapsTo_id _) differentiableOn_id
   refine ⟨g,bumps _ g (he'.mono (ball_subset_ball hp.le)),fun d=> he ⟨d.val,d.property.trans hp⟩, H _ hi g he' hV (fun t ht=> ?_)⟩
   rw [show g (↑t:ℂ)=f ⟨t,ht⟩ from he ⟨t,ht⟩]; exact h _

variable {t m N:ℕ}
-- If successive differences are small Mon. simply add from start.
lemma clasp (F:ℕ→ Row a →ℂ)(ha:0<a)(h:m≤N)(f:ℕ→ℝ)(hq:Summable f)(hx:∀ i,0≤ f i)(p:ℝ)(hb:Sail (desk a ha) (F m) p)(he:∀ i,m ≤ i→ i<N→ Sail (desk a ha) (fun z=> F (i+1) z-F i z) (f i)): Sail (desk a ha) (F N) (p+∑' i,f i):=by
    have ht k(h:m≤ k)(hk:k≤N) : Sail (desk a ha) (F k) (p+∑ i∈Finset.range k,f i):=by
        induction k,h using Nat.le_induction with
        | base=> exact hb.mono (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>hx i)))
        | succ i hi IH=>
           have hv:= (he i hi hk).plus (IH (i.le_succ.trans hk)); simp only [sub_add_cancel] at hv; rw [Finset.sum_range_succ]; exact hv.mono (le_of_eq (by ring))
    exact (ht N h le_rfl).mono (add_le_add_right (hq.sum_le_tsum _ (fun i _=>hx i)) _)

variable (S:Schedule)(hS:S.Gentle) (b:ℝ) (he:0<b)(ha:0<a)
include hS he
private lemma headTail (p q c:ℝ)(hv:Tendsto (fun i=>(S.scale (i+1))/S.scale i) atTop (𝓝 1))(h:p<c) (hp:q<c):∀ᶠ i in atTop, expS S q (i+1)+expS S p i≤expS S c i:=by
   let x i:= expS S q (i+1); have ht:Note S x q := (Note.bell_exp S q).scales hS
   let r:=(max p q+c)/2; have hr:p<r∧q<r∧r<c:= by unfold r; have ht:= max_lt h hp; constructor <;> first|linarith [le_max_left p q]|exact ⟨by linarith [le_max_right p q],by linarith⟩
   filter_upwards [ht.outweigh (Note.bell_exp S r) hr.2.1,(Note.bell_exp S p).outweigh (Note.bell_exp S r) hr.1, ((Note.bell_exp S r).extra (Note.bell_exp S r)).outweigh (Note.bell_exp S c) hr.2.2] with i hi hh hx
   exact (add_le_add hi hh).trans hx
variable (u:ℝ)(hu:0 < u)
include ha hu
lemma cordage : ∃ v:ℝ,∃ hv:0<v,∃ hl:v≤a,∃ p:ℝ, ∀ᶠ k in atTop,∀ N≥k,∀ f:ℕ→ Row a→ℂ, (∀ m,k ≤ m → m ≤N → Sail (desk a ha) (f m) (expS S b m)) → (∀ m,k ≤ m→m ≤N→∀ z:Row a, ‖f m z-f N z‖ ≤ expS S (-u) m)→ Sail (desk v hv) (fun z:Row v=> f N ⟨z.val,z.property.trans_le hl⟩) (expS S b k+p) :=by
   obtain ⟨v,hv,hl,hp⟩:= rescue (u/2) (b+1) ha (half_pos hu) (by linarith only [he]) S; let P:= rapid S ((u/2)/2) (by positivity); refine ⟨v,hv,hl,∑' i,expS S (-((u/2)/2)) i,?_⟩
   have hx:= barbell S hS; have h:b<b+1:=lt_add_of_pos_right _ zero_lt_one; have hh:-u< -(u/2):=by linarith only [hu]
   obtain ⟨k,hK⟩:= eventually_atTop.mp ((hp.and (headTail S hS b he b b (b+1) hx h h)).and (headTail S hS b he _ _ _ hx hh hh))
   filter_upwards [eventually_ge_atTop k] with i hi N hN f hF hf
   refine clasp (fun i (d:Row v)=> f i ⟨d.val,d.2.trans_le hl⟩) hv hN _ P (fun i=>(Real.exp_pos _).le) _ ?_ ?_
   · obtain ⟨g,hg,hE,hp⟩:= hF i le_rfl hN; have hh:DifferentiableOn ℂ g (ball 0 a):= hg _ id isOpen_ball (mapsTo_id _) differentiableOn_id; exact ⟨g,bumps _ _ (hh.mono (ball_subset_ball hl)),fun z=>hE ⟨z.val,z.2.trans_le hl⟩,fun z hz=> hp _ (ball_subset_ball hl hz)⟩
   intro m hm hm'; obtain ⟨⟨hA,hB⟩,hQ⟩:=hK m (hi.trans hm); have hJ:= hm.trans m.le_succ
   refine hA (fun z=> f (m+1) z-f m z) (((hF _ hJ hm').sub (hF _ hm hm'.le)).mono hB) (fun d=>?_)
   rw [show f (m+1) d-f m d=(f (m+1) d-f N d)-(f m d-f N d) by abel]
   exact (norm_sub_le ..).trans ((add_le_add (hf _ hJ hm' d) (hf _ hm hm'.le d)).trans hQ)
end YM.UVExtension.Tide
