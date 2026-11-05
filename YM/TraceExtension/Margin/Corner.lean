import YM.TraceExtension.Margin.Motion
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Lattice Matrix Precision Laurent Labels Source RG Wilson StressFlux
open Finset Kits Pressure Terrace Terrace.Glade Work Further.PhysicalPeriodLimitF933
open Shunt Wicket Perfect Turret Weir Extra.Histories Next.Foundations Planned.PrimaryIntegral295 Place
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s:Side}{Φ:Peat G s}{H:Hol G}
variable {F:Frame G 4}{Z:Frame G 5}{t:ℝ}{R:Rep G s}{X: Sway G s}
abbrev cardX (F:Frame G 4)(H:Hol G)(t:ℝ)(V:Sway G s)(a b:Axis):= DCard H F t (V a b 0)
abbrev cardY(Z:Frame G 5)(H:Hol G)(t:ℝ)(V:Sway G s)(b:Axis):= DCard H Z t (boom V b 0)
-- club purchases at W
abbrev Cubc (R:Rep G s)(t:ℝ)(f:Peat G s) : Prop := ClimateJ R f t (trayF t) (Zn.wideM t)
structure Club(R:Rep G s)(t:ℝ)(V:Sway G s):Prop where
    peek (b c:Axis): Cubc R t (V b c 0)
    pose (b c:Axis): Bounce (V b c)
    piece (b c:Axis): Cubc R t (elm b (V b c) 0)
    full (b:Axis): Cubc R t (boom V b 0)
lemma bail (a:Axis)(h:Club R t X)(hP:5 ≤ R.p.order)(hx:Nonwrapping (tempQ t (n:=s)) 0)(hG:G.Simple)(hs:40≤ s.val)(J:Jet G): Sock Z J (cardY Z H t X a)= pic F (cardX F H t X) a J:=by
    let V:= X; let S:= cardX F H t V; let Y:= cardY Z H t V; let u(i):loom G s:=⟨V i a 0,(h.peek i a).silk⟩
    have hL:JetTest H 0 (Z.coords.symm (Y a)) (Complex.ofRealCLM ∘ airT (fun i=>(u i).val)):= by
        have hu : ∀ i:Axis,V i a=fun k : Site s=> rj k (u i).val:= fun i=> funext fun k=> ((h.pose i a).trap k).symm
        have hx' : airT (fun i=> (u i).val)= boom V a 0:= by unfold boom airT; exact sum_congr rfl fun i _=> congr_arg (fun U=> elm i U 0) (hu i).symm
        rw[hx']; exact card_reads Z (Real_regular (h.full a).puff.regular) hP hx
    change Labels.read J (Z.coords.symm (Y a)).val=pic F S a J; rw[readable u (fun i=> (h.peek i a).puff.regular.sites) hx hs hG hL,Complex.ofReal_sum]; refine Finset.sum_congr rfl fun i _=>?_
    exact (sprig5 _ _ (u i) (show JetTest H 0 (F.coords.symm (S i a)) (filmR (u i).val) from card_reads F (Real_regular (h.peek i a).puff.regular) (by omega) hx) hG).symm
structure Walt (F:Frame G 4)(Z:Frame G 5)(H:Hol G)(x:ℝ)(X:Sway G s)(w:Fin 3→ℝ): Prop where
    truth(a b:Axis): Plot (Prism F) (cardX F H x X) a b=F.coords (stress G (Fin.cons 0 w) a b)
    tempo(b:Axis): Reed (Prism Z) (cardY Z H x X) b=Z.coords ((bareVector w).val b)
variable (h: Club R t X)(hn:5≤R.p.order)(hx:Nonwrapping (tempQ t (n:=s)) 0)(hs:40 ≤ s.val)(hG:G.Simple)
include h hn hx hs hG
lemma scepter {w}(hw:∀ a b:Axis, Plot (Prism F) (cardX F H t X) a b= F.coords (stress G (Fin.cons 0 w) a b)): Walt F Z H t X w:=by
    let V:=cardX F H t X; let Y:=cardY Z H t X; let L(u:F.Coeff):= F.coords.symm u; let A (i j:Axis):loom G s:=⟨X i j 0,(h.peek i j).silk⟩
    refine ⟨hw,fun i=> ?_⟩; let q:= Reed (Prism Z) Y i; apply Z.coords.symm.injective; rw[LinearEquiv.symm_apply_apply]; apply label_ext; intro J
    have h₁(i j:Axis):= Real_regular (h.peek i j).puff.regular
    change Sock Z J q=_; rw[show Sock Z J q=_ from rot_v F Z A (V:=V) (Y:=Y) (fun i j=> card_reads F (h₁ i j) (by omega) hx) (fun i=>card_realV Z (Real_regular (h.full i).puff.regular) hn) (fun i j=>card_realV F (h₁ i j) (by omega)) hG (fun i=> bail i h hn hx hG hs) J i]
    unfold V pic; refine Eq.trans (Finset.sum_congr (g:=fun a=> prance J w i a) rfl ?_) (show _=Labels.read J _ from pranced ..); intro a _; rw[hw]; change accord J a (F.coords.symm (F.coords _))=_; rw[LinearEquiv.symm_apply_apply];rfl
lemma pruned (hp:∀ i j:Axis,cardX F H t X i j=cardX F H t X j i):∃ w,Walt F Z H t X w:=by
    obtain ⟨w,hw⟩:=wings F _ hp (fun i j=> Margin.card_zero F (Real_regular (h.peek i j).puff.regular) (by omega) hx (h.peek i j).silk) hG
    exact ⟨w,scepter h hn hx hs hG fun i j=> (hw i j).symm⟩
end YM.Trace.Margin
