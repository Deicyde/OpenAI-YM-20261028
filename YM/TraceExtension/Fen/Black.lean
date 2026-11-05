import YM.TraceExtension.Fen.Locus
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Fen
open Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Function Filter Shepherd AnalyticBridge VerifiedReset Drupes
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side} {R:Rep G n}{d k:ℕ}{σ A C:ℝ}{X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]{U:X→ Config G n} {x:X}
lemma rollA (s:Seat n)(h:∀ i,Allows d (fun y=>G.mat (U y i)) x A): ∀ i,Allows d (fun y=> G.mat (s.view (U y) i)) x A:=by
    intro i; simp only [Seat.view,pull, Step.read]; split; exact Allows.inverse (f:=fun y=> U y _) (h _); exact h _
lemma pardon(G:Gauge)(A:ℝ)(d:ℕ)(ha:0 ≤ A): ∃ f:ℕ→ℝ,MarksP f ∧ ∀ (X:Type) [NormedAddCommGroup X] [NormedSpace ℝ X](n:Side) (o:Site n)(p:RG.Slot)(l:ℕ), p.length ≤ l→∀ (U:X→ Config G n) (x:X)(h:∀ i,Allows d (fun y=>G.mat (U y i)) x A), Allows d (fun y=> p.atSite (U y) o) x (f l):=by
   obtain ⟨C,hC,H⟩:= shaders G d
   let S(l):= composeCost d C (travelCost G d l A); let T:= oneL G * travelCost G d 4 A; have hT:0≤T:=mul_nonneg (hOneL G) (travel_non _ _ _ _ ha); let L:=(ContinuousLinearMap.apply ℝ G.Color (E:=G.Color)).flip; let D(l):=2^d*‖L‖ * S l*T
   refine ⟨D,?_ ,?_⟩
   · exact ((token _ (show 0≤ 2^d * ‖L‖ by positivity)).pair ((token _ (by linarith only[hC])).composeM d (MarksP.travelM _ d id A ha poles))).pair (token _ hT)
   intro X _ _ n o p l hl U x hu; let F:= fun y=> travel (U y) o p.walk; let u:=Work.F03.slotFace p o; let M(y):= G.mat (faceValue (U y) u)
   have hx:Allows d M x (travelCost G d 4 A):= travel_jets (U:=U) hu u.1 (w:=square u.2.val.1 u.2.val.2) (by simp[square]); have hy:= travel_jets (U:=U) hu o (w:=p.walk) (by unfold Slot.length at hl; omega : p.walk.length ≤ l)
   apply ((Allows.bilinear (f:=jetAd G ∘ G.mat ∘ F) L (Allows.comp (f:=fun y=>G.mat (F y)) (H (F x)) hy) (hx.linear (cbr G) le_rfl) le_rfl):Allows d _ x (D l)).germ
   filter_upwards with y
   rw [Work.F03.atSite_path,identifies]; exact congr_arg (fun z: (G.Color →L[ℝ] G.Color)=> z _) (turned (F y)|>.symm)
private lemma stamp(G:Gauge)(d:ℕ)(A:ℝ)(ha:0≤ A):∃ C:ℝ,1≤ C∧∀ (X:Type) [NormedAddCommGroup X] [NormedSpace ℝ X](n:Side)(o:Site n)(p:PlaqAxes)(U:X→ Config G n)(x:X)(h:∀ i, Allows d (fun y=>G.mat (U y i)) x A), Allows d (fun y=> G.price (faceValue (U y) (o,p))) x C:=by
    let C:=priceCost G (travelCost G d 4 A)
    refine ⟨max 1 C,le_max_left ..,?_⟩; intro X _ _ n o p U x h
    exact (Allows.price (f:=fun y=>faceValue (U y) (o,p)) (travel_jets (U:=U) h o (w:=square p.val.1 p.val.2) (by simp [square]:List.length _≤ 4))).mono (le_max_right ..)
lemma proton(G:Gauge)(k:ℕ)(A:ℝ)(ha:0 ≤ A): ∃ D:ℕ→ℝ, MarksP D ∧ ∀ (X:Type)[NormedAddCommGroup X] [NormedSpace ℝ X](n:Side)(o:Site n)(p:Low)(W:PathData G)(U:X→ Config G n)(x:X)(h:∀ i, Allows k (fun y=>G.mat (U y i)) x A), Allows k (fun y=> Low.plain W p o (U y)) x (D (p.length W)):=by
    obtain ⟨D,hD,H⟩:= pardon G A k ha; obtain ⟨E,hE,He⟩:= stamp G k A ha
    let L:= innerSL ℝ (E:=G.Color); let F i:= |(1/2:ℝ)| * (2^k* ‖L‖ * D i*D i)
    have hf:MarksP F:= (token _ (abs_nonneg _)).pair (((token (2^k* ‖L‖) (by positivity)).pair hD).pair hD)
    refine ⟨_,hf.booth (token E (by positivity)),?_⟩; intro X _ _ n o p W U x h
    cases he:p.2 with
    | inl j=>
       unfold Low.plain; rw [he]; exact (He X n o p.1 U x h).mono (le_add_of_nonneg_left (hf.1 _))
    | inr j=>
       let w:=Low.left W p j; let a:=Low.right W p j
       have h':Allows k (fun y=>w.atSite (U y) o) x (D (p.length W)):= H X n o w (p.length W) (by simp [Low.length,he,w]) U x h
       have hh:= H X n o a (p.length W) (by simp [Low.length,a,he]) U x h
       refine (((h'.bilinear L hh le_rfl).smul (1/2)).mono (le_add_of_nonneg_right (zero_le_one.trans hE))).germ ?_
       filter_upwards with y; unfold Low.plain; rw[he]; change (1/2:ℝ)*inner ℝ (w.atSite (U y) o) (a.atSite (U y) o)=_; change (1/2:ℝ)*inner ℝ (w.atSite (U y) o) (a.atSite (U y) o)=inner ℝ (w.atSite (U y) o) (a.atSite (U y) o)/2; ring
lemma roundBill (G:Gauge)(A:ℝ)(ha:0 ≤ A)(k m:ℕ):∃ D:ℕ→ℝ, MarksP D ∧∀ (X:Type)[NormedAddCommGroup X] [NormedSpace ℝ X](n:Side)(o:Site n)(p:Atom G m)(U:X→ Config G n)(x:X)(h:∀ i, Allows k (fun y=>G.mat (U y i)) x A), Allows k (fun y=> p.unmasked (U y) o) x (p.magnitude * D p.length):=by
    obtain ⟨D,hD,H⟩:= pardon G A k ha; let TP (i:G.ColorIndex):G.Color→L[ℝ] ℝ:=EuclideanSpace.proj i; let W:= ∑ i:G.ColorIndex, ‖TP i‖; have hw:0 ≤ W:= sum_nonneg fun _ _=>norm_nonneg _; let V(r:ℕ):=W*D r
    refine ⟨_, ((token ((2:ℝ)^k) (by positivity)).pair ((token W hw).pair hD)).tier m,?_⟩; intro X _ _ n o p U x hu
    have hv(i:Fin m)(t:G.ColorIndex): Allows k (fun y=>(p.leg i).atSite (U y) o t) x (V p.length):= (H X n o _ p.length (single_le_sum (f:=fun i=> (p.leg i).length) (fun i _=>Nat.zero_le _) (mem_univ i)) U x hu).linear (TP t) (single_le_sum (f:=fun j=>‖TP j‖) (fun i _=>norm_nonneg _) (mem_univ t))
    let Q(i):=(2^k*V i)^m; have hz(g:Fin m→ G.ColorIndex)(s:Finset (Fin m)): Allows k (fun y=> ∏ i∈s,(p.leg i).atSite (U y) o (g i)) x ((2^k*V p.length)^s.card):=by
        induction s using Finset.induction with
        | empty=> simpa using! allows_const (C:=1) x (v:=(1:ℝ)) (by norm_num) (n:=k)
        | insert i s hi ih=>
          simp_rw[prod_insert hi,card_insert_of_notMem hi,pow_succ']
          have he:= (hv i (g i)).bilinear (ContinuousLinearMap.mul ℝ ℝ) ih (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)
          rw[mul_one] at he; exact he
    have hi(g:Fin m→G.ColorIndex):Allows k (fun y=> ∏ i,(p.leg i).atSite (U y) o (g i)) x (Q p.length):=by simpa [Q] using hz g univ
    have hz:= allows_sum (f:=fun (g:Fin m→G.ColorIndex) y=> p.coeff g * ∏ i,(p.leg i).atSite (U y) o (g i)) (s:=univ) (fun i _=> (hi i).smul (p.coeff i)); change Allows k _ x (∑ i,_*Q p.length) at hz
    rw[← Finset.sum_mul] at hz; exact hz
lemma black (G:Gauge)(A:ℝ)(d:ℕ)(ha:0≤ A):∃ f:ℕ→ℝ, MarksP f ∧ ∀ (X:Type)[NormedAddCommGroup X] [NormedSpace ℝ X]{n:Side}(W:Rep G n)(U:X→ Config G n)(x:X)(h:∀ i, Allows d (fun y=>G.mat (U y i)) x A) (s:Seat n)(p:Barley), Allows d (fun y=> fer W s p (U y)) x (port W p * f (mote W p)):=by
    obtain ⟨D,hD,Hd⟩:= proton G d A ha
    choose f hf H using roundBill G A ha d
    let F(i):=D i+∑ j∈range 5,f j i
    refine ⟨F,hD.booth (mark_sum _ _ (fun i _=>hf i)),?_⟩; intro X _ _ n W U x h s p; let V:=Seat.view s ∘ U
    have hu(i):Allows d (fun y=>G.mat (V y i)) x A:=rollA s h i
    have ht:Allows d (fun y=>ul W.path W.clip p 0 (V y)) x (port W p * F (mote W p)):=by
       cases p with
       | inl j=> exact ((Hd X n _ j W.path V x hu).smul (j.mark W.path W.clip)).mono (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sum_nonneg fun i _=> (hf i).1 _)) (abs_nonneg (j.mark W.path W.clip)))
       | inr j=>
          have hx: rowD j< 5:=by cases j with
             | inl k=> cases k <;> norm_num [rowD,High.arity]
             | inr k=> change 2 < (5:ℕ); omega
          simp_rw [fresh_loop]; apply (H _ X n 0 (tooth W j) V x hu).mono
          exact mul_le_mul_of_nonneg_left ((single_le_sum (f:=fun i=> f i _) (fun i _=> (hf i).1 _) (mem_range.mpr hx)).trans (le_add_of_nonneg_left (hD.1 _))) (ports_n W (.inr j))
    refine (ht.smul VerifiedReset.factor).mono (mul_le_of_le_one_left ht.nonneg ?_); rw[abs_of_nonneg factor_pos.le]; exact factor_le
end YM.Trace.Fen
